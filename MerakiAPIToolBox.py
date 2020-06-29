import meraki as mer
import csv
from tabulate import tabulate
import os
import json
import time
from mac_vendor_lookup import MacLookup as maclookup
from termcolor import colored, cprint
from concurrent import futures
from netaddr import *
import netaddr
import re
import socket
import readline

'''
Deprecated Imports
from ratelimit import limits, RateLimitException
from backoff import on_exception, expo
import random
import math
'''

''''''''''''''''''''''''
###     GLOBALS      ###
''''''''''''''''''''''''
# Verbosity
VERBOSE = False
# Indentation
INDENT = 0
# Logs go into a log directory and are $(unix time).log
LOGDIR = os.path.join(os.getcwd(), "logs")
LOGFILEPATH = os.path.join(LOGDIR, str(int(time.time())) + ".log")
# Meraki api calls generate a lot of cruff so we will jam them into here
MERLOGDIR = os.path.join(os.getcwd(), "meraki_logs")
if not os.path.isdir(LOGDIR):
    os.mkdir(LOGDIR)
    LOGFILE = open(LOGFILEPATH, "w")
else:
    LOGFILE = open(LOGFILEPATH, "w")
if not os.path.isdir(MERLOGDIR):
    os.mkdir(MERLOGDIR)

'''''''''''''''''''''''''''
###  UTILITY FUNCTIONS  ###
'''''''''''''''''''''''''''


# Controls verbose output
def printv(m):
    if type(m) is list:
        m = "[" + ', '.join(str(x) for x in m) + "]"
    if VERBOSE:
        printi("VERBOSE: " + str(m))
        LOGFILE.write("VERBOSE: " + str(m) + "\n")
    else:
        LOGFILE.write("VERBOSE: " + str(m) + "\n")


# Indents output for us
def printi(m):
    for line in m.split("\n"):
        print("%s%s" % ("\t" * INDENT, line))


# Allows us to dump any dict into a csv format file
def dictToCSV(dic, filename):
    keys = dic[0].keys()
    with open(filename, 'w', encoding='utf8', newline='') as output_file:
        dict_writer = csv.DictWriter(output_file, fieldnames=dic[0].keys())
        dict_writer.writeheader()
        dict_writer.writerows(dic)


# Removes a key from a dictionary
def removeKey(d, key):
    r = dict(d)
    del r[key]
    return r


# Formats a given dict that we can then use to send to the API
def formatDict(d, port):
    # I gave up trying to make the null/None values work so if they are null/None they get burned to the ground
    e = dict(d)
    for k, v in d.items():
        # There is a lot of information that the API returns to us that we do not need
        if (v is None) or \
                (v == '') or \
                (v == []) or \
                (port is True and 'number' in k) or \
                (port is False and 'serial' in k):
            del e[k]
    return e


# If we are passed a list of macs we can sanitize our inputs using this
def formatMACS(macaddrs, filename):
    if filename:
        path = os.path.join(os.getcwd(), filename)
        with open(path) as f:
            macaddrs = f.readlines()

    indexes = [2, 5, 8, 11, 14]
    newmacaddrs = []
    for macaddr in macaddrs:
        # Remove whitespace, make it all lowercase, and remove any - or :
        mac = str(macaddr).strip().upper().replace('-', '').replace(':', '')
        for x in indexes:
            if len(mac) <= x:
                break
            mac = mac[:x] + ":" + mac[x:]

        newmacaddrs.append(mac)

    return newmacaddrs


# For when we need just a single device.
def getDevice(dashboard, networks, name):
    return [device for network in networks for device in dashboard.devices.getNetworkDevices(networkId=network['id'])
            if device['name'].lower() == name.lower()]


# Organization => Networks => Devices => Clients
# This will return to us a list of networks
# If a filter exists, it will remove any networks in the filter
def getNetworks(dashboard, filterOut):
    networks = []
    for network in dashboard.networks.getOrganizationNetworks(organizationId=orgID):
        '''
         not any(x in network['name'] for x in filterOut)
         not => negates the statement
         any() => checks if there are any true values
         x in network['name'] => iterates through all values of network['name'] and assigns their values to x
         x in filterOut => for each value of x check if it is in filterOut
        '''
        if filterOut is None:
            networks.append(network)
            continue
        if not any(x.lower() in network['name'].lower() for filters in filterOut for x in filters):
            printv("Adding the network %s" % network['name'])
            networks.append(network)

    return networks


# Returns a list of all devices across all networks
# If any of the filters are in a device's LAN IP, Serial, Name, Tags, or Model, then it is added to our device list
def getDevices(dashboard, networks, deviceFilter, devices=None, filterOut=True, filterIn=False):
    if deviceFilter is not None and len(deviceFilter) >= 1:
        if type(deviceFilter[0]) is not list:
            printv("Applying the filter of \"%s\"" % ','.join(deviceFilter))
        else:
            deviceFilter = [f for filt in deviceFilter for f in filt]
            printv("Applying the filter from list of \"%s\"" % ','.join(deviceFilter))
    else:
        printv("There was no device filter")
    if devices is None:
        devices = []
        printv("Creating a list of devices from our networks")
        for network in networks:
            for device in dashboard.devices.getNetworkDevices(networkId=network['id']):
                if 'name' not in device:
                    device['name'] = device['mac']
                devices.append(device)
        printv("New devices length %d" % len(devices))
    devFilter = []
    newDevices = []
    if deviceFilter is not None and len(deviceFilter) >= 1:
        printv("Formatting the filters")
        for filter in deviceFilter:
            if is_ip(filter):
                if '/' not in filter:
                    devFilter.append(IPNetwork(filter + '/32'))
            else:
                devFilter.append(filter.lower())
        for device in devices:
            if deviceFilter is None:
                printv("Adding the device %s" % device['name'])
                newDevices.append(device)
                continue
            else:
                filtered = False
                for filter in devFilter:
                    if filter in str(device['name']).lower() or \
                            filter in str(device['model']).lower() or \
                            filter in str(device['serial']).lower() or \
                            (type(filter) is IPNetwork and IPAddress(device['lanIp']) in filter):
                        # We can not expect all switches to be tagged so we do a special check for it
                        if 'tag' in device:
                            if any(tag for tag in device['tags'].strip().split(' ') if tag in [str(f) for f in filter]):
                                filtered = True
                                break
                        else:
                            printv("%s does not have any tags so we could not check the filter against it"
                                   % device['name'])
                            filtered = True
                            break
                # One of the devices values matches a passed in filter so now we check if we filter in or out
                # Filtering the device out is our default
                if not filtered and filterOut:
                    printv("Adding the device %s" % device['name'])
                    newDevices.append(device)
                if filtered and filterIn:
                    printv("Adding the device %s" % device['name'])
                    newDevices.append(device)
        return newDevices
    else:
        printv("Returning devices")
        return devices


# Will tell us which network a switch belongs to
def getDeviceNetwork(serial, networks):
    for network in networks:
        for switch in dashboard.devices.getNetworkDevices(networkId=network['id']):
            if switch['serial'] == serial:
                return network


# Checks if device exists and returns true and the device if found or false and none otherwise
def is_device(devices, filter):
    printv("Looking for a device with the filter of %s" % filter)
    for device in devices:
        if 'serial' in device and device['serial'].lower() == filter.lower() or \
                'lanIp' in device and device['lanIp'] == filter or \
                'name' in device and device['name'].lower() == filter.lower():
            return device, True
    return None, False


# Used when checking if vlans is all or when port number is not an int but something like g1
def is_int(x):
    try:
        num = int(x)
    except ValueError:
        return False
    return True


# Used to determine if a given port exists on a switch
def is_port(dashboard, device, filter):
    printv("Look for port %s on %s" % (filter, device['name']))
    for port in dashboard.switch_ports.getDeviceSwitchPorts(device['serial']):
        if str(port['number']) == str(filter):
            return port, True
    return None, False


def is_ip(i):
    try:
        if '/' not in i:
            i += '/32'
            j = IPNetwork(i)
        else:
            j = IPNetwork(i)
        return True
    except netaddr.core.AddrFormatError or ValueError:
        return False


# In our main function almost all of its sub-functions will need the networks and devices variable correctly set
def checkVariables(devices, networks, networkFilter, deviceFilter):
    if not networks:
        printi("Getting networks")
        networks = getNetworks(dashboard=dashboard, filterOut=networkFilter)
        networks.sort(key=lambda x: x['name'])
    if not devices:
        printi("Finding devices in networks")
        devices = getDevices(dashboard=dashboard, networks=networks, deviceFilter=deviceFilter)
        devices.sort(key=lambda x: x['name'])
    return networks, devices


# Breaks our very long device list up into X columns making it easier to read
def printDevices(devices, columns, detailed=False):
    # If we are printing just a single switch
    if type(devices) is not list:
        filter = ['name', 'url', 'model', 'mac', 'tags', 'serial', 'networkId']
        temp = dict()
        for key in filter:
            if key not in devices:
                temp[key] = 'None'
        for k, v in devices.items():
            if k in filter:
                temp[k] = v
        printi(json.dumps(temp, indent=4))
    elif detailed:
        data = []
        for device in devices:
            data.append([device['name'], device['serial'], device['model'],
                         device['lanIp'], device['mac'], device['url']])
        data.sort(key=lambda x: x[0])
        data.insert(0, ["Name", "Serial", 'Model', 'IP', 'MAC', 'URL'])
        printi(tabulate(data, headers='firstrow'))
    else:
        printi(tabulate(divideChunks([device['name'] for device in devices], columns)))


# Allows us to split a list up into chunks
def divideChunks(lst, chunks):
    # looping till length l
    for i in range(0, len(lst), chunks):
        yield lst[i:i + chunks]


# Confirms we have a dashboard instance
def getDashboard(apikey, maxRetry):
    try:
        dashboard = mer.DashboardAPI(api_key=apikey,
                                     print_console=False,
                                     maximum_retries=maxRetry,
                                     wait_on_rate_limit=True,
                                     log_path=MERLOGDIR)
        return dashboard, True
    except:
        return None, None


# returns a properly formatted mac address
def formatMACAddr(mac):
    indexes = [2, 5, 8, 11, 14]
    # Remove whitespace, make it all lowercase, and remove any - or :
    macaddr = str(mac).strip().upper().replace('-', '').replace(':', '')
    for x in indexes:
        if len(mac) <= x:
            break
        macaddr = macaddr[:x] + ":" + macaddr[x:]
    printv(macaddr)
    return macaddr


# Utility function that pairs with the gatherMacs primary function to locate a mac address on our network
def findMacs(macDict, macs, vendors):
    data = []
    if bool(vendors):
        for ven in macDict.keys():
            # sorry not sorry
            if any(vend for vend in vendors if ven.lower() in vend.lower()):
                printv("if statement resulted in true for the vednor \"%s\"" % ven)
                for macaddr in macDict[ven]:
                    for deviceName, port in macDict[ven][macaddr]:
                        data.append([ven, macaddr, deviceName, port])
    if bool(macs):
        for ven in macDict.keys():
            for macaddr in macDict[ven]:
                if any(mac for mac in macs if formatMACAddr(macaddr) in formatMACAddr(mac)):
                    printv("if statement resulted in true for the mac \"%s\"" % formatMACAddr(macaddr))
                    for deviceName, port in macDict[ven][macaddr]:
                        data.append([ven, macaddr, deviceName, port])
    data.insert(0, ['Vendor', 'MacAddr', 'Device', 'Port'])
    printi(tabulate(data, headers='firstrow'))


# Helper function to print mac data
def printMacs(macDict):
    data = []
    for vendor in macDict.keys():
        for mac in macDict[vendor]:
            for location in macDict[vendor][mac]:
                data.append([
                    vendor,
                    mac,
                    location[0],
                    location[1]
                ])
    data.insert(0, ['Vendor', 'MacAddr', 'Device', 'Port'])
    printi(tabulate(data, headers='firstrow'))


# Helper function used for printing out switch port information
def printSwitchPorts(switchPorts):
    data = []
    for k in switchPorts.keys():
        for ports in switchPorts[k]:
            data.append([k] + [p for p in ports.values()])
    data.insert(0, ['Switch', 'Number', 'Name', 'Tags', 'Enabled', 'POE Enabled', 'Type', 'VLAN',
                    'Voice VLAN', 'Allowed VLANs', 'RSTP Enabled', 'STP Guard'])
    printi(tabulate(data, headers='firstrow'))


def getNetwork(networks):
    printi("Please select a network to work with")
    for x, network in enumerate(networks):
        printi("%d: %s" % (x + 1, network['name']))
    network = input(prompt)
    networkId = None
    while not is_int(network) and (1 < int(network) > len(networks)):
        printi("Invalid choice. Please choose a number from 1 to %d or 0 to go back" % len(networks))
        network = input(prompt)
        if network == '0':
            return None
    if network == '0':
        return None
    else:
        return networks[int(network) - 1]


'''
### PRIMARY FUNCTIONS
'''


# Original logic written by Nico Darrow of Meraki
# Translated and adjusted for this API Tool by Adam Littrell
# Switches need to be unstacked before migrating
# Port aggregation isn't supported (aggregated ports will be split)
# L3 Interfaces / DHCP scopes / ACLs will not be migrated
def migrateSwitches(dashboard, srcNetwork, dstNetwork, tag, whatIf):
    srcNetId = srcNetwork['id']
    dstNetId = dstNetwork['id']
    if whatIf:
        printv("We are doing a switch migration test run")
        printv("We will be migrating the switches from %s with the tag of %s to %s" % (
            srcNetwork['name'], tag, dstNetwork['name']
        ))
    else:
        printv("We are doing a live switch migration")
        printv("We will be migrating the switches from %s with the tag of %s to %s" % (
            srcNetwork['name'], tag, dstNetwork['name']
        ))
    inScopeDevices = []
    for device in dashboard.devices.getNetworkDevices(srcNetId):
        if 'tag' in device and tag in device['tag']:
            inScopeDevices.append(device)
    if whatIf:
        printi("The following devices would be moved")
        printDevices(inScopeDevices, 5)
        return

    # Migrating the switches
    for device in inScopeDevices:
        # Making our backups
        printv("Making our backup for %s" % device['name'])
        filename = str(int(time.time())) + "_" + device['name'] + "_backup.json"
        ports = dashboard.switch_ports.getDeviceSwitchPorts(device['serial'])
        device['ports'] = ports
        with open(filename, 'w') as f:
            printv("Saving %s configuration to file" % device['name'])
            json.dump(device, f)

        # Unclaiming the devices for source network and claiming them in destination network
        printv("Migrating %s to new network" % device['name'])
        dashboard.devices.removeNetworkDevice(srcNetId, serial=device['serial'])
        dashboard.devices.claimNetworkDevices(dstNetId, serial=device['serial'])

        # Restoring port configuration on the switch
        for port in ports:
            p = formatDict(port, port=True)
            dashboard.switch_ports.updateDeviceSwitchPort(serial=device['serial'], number=port['number'], **p)

    printi("Migration complete")


# Transfers the port configuration from point A to point B
def copySwitchPortConfig(dashboard, sSwitch, sPort, dSwitch, dPort):
    # First we get the source switch port config
    sourcePort = dashboard.switch_ports.getDeviceSwitchPort(sSwitch['serial'], number=sPort['number'])
    printv("Original source port configuration (null = None)")
    printv(json.dumps(sourcePort, indent=4))
    printv("Original destination port configuration (null = None)")
    destPort = dashboard.switch_ports.getDeviceSwitchPort(dSwitch['serial'], number=dPort['number'])
    printv(json.dumps(destPort, indent=4))
    # Then we remove the number key from the dict
    kwargsDict = formatDict(sourcePort, port=True)
    printv("Formatted configuration")
    printv(json.dumps(kwargsDict, indent=4))
    # Lastly we pass our dict, ie our source port config, over to the destination port configuration
    dashboard.switch_ports.updateDeviceSwitchPort(serial=dSwitch['serial'], number=dPort['number'], **kwargsDict)
    destPort = dashboard.switch_ports.getDeviceSwitchPort(dSwitch['serial'], number=dPort['number'])
    printv("New destination port configuration")
    printv(json.dumps(destPort, indent=4))


# This needs to be re-written and has been pulled out of rotation until it can be re-written
# Needs to have standardized inputs, less try catch, and vlan formatting moved to utility function
# getSwitchVLANS function contains the log we will need
def findPortsByVLAN(dashboard, vlan, networks):
    data = []
    data.append(['Switch', 'Port', 'Network', 'URL'])

    for network in networks:
        if "DC" in network['name'] and "wireless" not in network['name']:

            tmp = dashboard.devices.getNetworkDevices(networkId=network['id'])
            devices = sorted(tmp, key=lambda k: k['name'])

            for device in devices:
                try:
                    for port in dashboard.switch_ports.getDeviceSwitchPorts(device['serial']):
                        vlanList = []
                        for vlan in str(port['allowedVlans']).split(','):
                            if "-" in vlan:
                                for i in range(int(vlan.split("-")[0]), int(vlan.split("-")[1])):
                                    if int(i) not in vlanList:
                                        vlanList.append(int(i))
                                        vlanList.sort()
                            else:
                                if ("all" not in vlan) and (int(vlan) not in vlanList):
                                    vlanList.append(int(vlan))
                                    vlanList.sort()

                        if vlan in vlanList:
                            data.append([device['name'],
                                         str(port['number']),
                                         network['name'],
                                         device['url']
                                         ])
                    printv("Finished with the \"%s\" switch" % device['name'])
                except:
                    printv("We ran into an error with the \"%s\" switch" % device['name'])

    printi(tabulate(data, headers='firstrow'))


# Will return a list of all vlans on all switches
def getSwitchVLANS(devices):
    vlans = dict()
    data = []
    for device in devices:
        # We use a set since we dont want duplicates and itll make our code easier to read
        vlans[device['name']] = set()
        for port in dashboard.switch_ports.getDeviceSwitchPorts(device['serial']):
            # port['vlan']
            if 'vlan' in port and is_int(port['vlan']):
                vlans[device['name']].add(int(port['vlan']))

            # port['allowedVlans']
            for vlan in str(port['allowedVlans']).split(','):
                # 'allowedVlans': '20-21,78,81,1prompt,128,130,150,270,296,328'
                if "-" in vlan:
                    for i in range(int(vlan.split("-")[0]), int(vlan.split("-")[1])):
                        vlans[device['name']].add(i)
                elif "all" not in str(vlan):
                    vlans[device['name']].add(int(vlan))
        vlans[device['name']] = sorted(vlans[device['name']])

    # We are returning the dict and will handle the printing elsewhere
    return vlans


# If a port is connected then it is considered in use.  Takes number of in use and divides it by total
# Take this information with a grain of salt because there is a lot of assumptions I skip out of laziness
# Need to add a feature that will print out which switches have 1-10,10-20,20-30,30-35,35-40,40-48 ports connected
def getPortUsageStats(dashboard, devices):
    inUsePorts = 0
    totalPorts = 0
    waste_check = []
    for device in devices:
        deviceInUse = 0
        deviceTotal = 0
        for port in dashboard.switch_ports.getDeviceSwitchPortStatuses(serial=device['serial']):
            if port['status'] == "Connected":
                inUsePorts += 1
                totalPorts += 1
                deviceInUse += 1
                deviceTotal += 1
            else:
                totalPorts += 1
                deviceTotal += 1
        printv(device['name'] + " is at " + "{:.2%}".format(deviceInUse / deviceTotal) + " allocation")
        percent = deviceInUse / deviceTotal
        if percent <= 1.1:
            waste_check.append([device['name'],
                                deviceInUse,
                                deviceTotal,
                                "{:.2%}".format(percent)])

    waste_check.sort(key=(lambda x: x[1] / x[2]))
    waste_check.insert(0, ["Name", "In Use", "Total", "Allocation"])
    printi("Total Switches: %s" % len(devices))
    printi("Total Ports: %s" % totalPorts)
    printi("In Use Ports: %s" % inUsePorts)
    printi("Port allocation: " + "{:.2%}".format(inUsePorts / totalPorts))
    printi("Switches worth investigating:")
    printi(tabulate(waste_check, headers='firstrow'))


# This will gather all the MAC address seen by all the given switches
# We can then pass this information over to a lookup function and thus have an easy way to locate macs
# The use of multithreading is crucial here for without it, this will take over 4 minutes to complete
def gatherMacs(dashboard, devices, networks):
    '''
    Notes:
        I could never get this to work properly.  Despite setting it to be 5 calls per second as per Meraki rules,
        I was still getting 429 rate limit errors.  I messed around with this a lot, and even told the Dashboard API
        library to wait and try again after the 429 errors but with no luck.  I decided to put making the processing
        part of the function multithreaded.  It goes by about as fast if I double the thread limit

    # The api only allows us 5 calls per second
    # By having this limiter and exponential back-off, we can maximize speed without worry
    @on_exception(expo, RateLimitException, max_tries=10)
    @limits(calls=5, period=1)
    def callAPI(device, networkId, clients, lldp):
        error = 1
        while True:
            try:
                if clients:
                    ret = dashboard.clients.getDeviceClients(serial=device['serial'], timespan=1296000)
                if lldp:
                    ret = dashboard.devices.getNetworkDeviceLldp_cdp(networkId=networkId,
                                                                       serial=device['serial'],
                                                                       timespan=1296000)
                print("%s LEAVING API CALL" % device['name'])
                return ret
            except:
                print("%s GOT ERROR FOR %d TIME" % (device['name'], error))
                error += 1
                time.sleep(random.uniform(3, 5))
    '''

    # The first place to look for a MAC is LLDP/CDP
    def processDeviceLLDP(device, ports, networkId):

        printv("%s is in LLDP" % device['name'])

        # Getting our master dicts created
        masterDic = dict()
        masterDic['Unknown'] = dict()

        printv("Working with %s" % device['name'])
        printv("Checking LLDP/CDP information")

        # Using our rate limit function to call our api and get our LLDP information
        # ports = callAPI(device=device, networkId=networkId, lldp=True, clients=False)

        if 'ports' in ports and bool(ports):
            # Iterating through all the ports and gathering their information
            for port in ports['ports']:
                # LLDP
                if 'lldp' in ports['ports'][port]:
                    # Getting MAC
                    if 'portId' in ports['ports'][port]['lldp'] and bool(ports['ports'][port]['lldp']['portId']):
                        portIDCheck = ports['ports'][port]['lldp']['portId']
                        if len(str(portIDCheck).replace(':', '')) == 12:
                            portid = formatMACAddr(portIDCheck)
                            # Seeing if we can get a vendor
                            try:
                                vendor = maclookup().lookup(portid)
                                # Checking if we have a vendor dict
                                if vendor not in masterDic:
                                    masterDic[vendor] = dict()
                                # Checking if we have a MAC array in the vendor
                                if portid not in masterDic[vendor]:
                                    masterDic[vendor][portid] = []
                                # Checking if we already have the switch,port tuple in the array
                                if (device['name'], port) not in masterDic[vendor][portid]:
                                    masterDic[vendor][portid].append((device['name'], port))
                                else:
                                    printv("(%s,%s) already exists for the mac %s for the vendor %s" %
                                           (device['name'], port, portid, vendor))
                            except:
                                printv("On switch %s port %s we could not get a vendor for the mac %s" %
                                       (device['name'], port, portid))
                                if portid not in masterDic['Unknown']:
                                    masterDic['Unknown'][portid] = []
                                if (device['name'], port) not in masterDic['Unknown'][portid]:
                                    masterDic['Unknown'][portid].append((device['name'], port))
                                else:
                                    printv("(%s,%s) already exists for the mac %s in the unknowns" %
                                           (device['name'], port, portid))
                # CDP
                if 'cdp' in ports['ports'][port]:
                    # Getting MAC
                    if 'deviceId' in ports['ports'][port]['cdp']:
                        deviceIDCheck = ports['ports'][port]['cdp']['deviceId']
                        if len(str(deviceIDCheck).replace(':', '')) == 12:
                            deviceId = formatMACAddr(deviceIDCheck)
                            # Seeing if we can get a vendor
                            try:
                                vendor = maclookup().lookup(deviceId)
                                # Checking if we have a vendor dict
                                if vendor not in masterDic:
                                    masterDic[vendor] = dict()
                                # Checking if we have a MAC array in the vendor
                                if deviceId not in masterDic[vendor]:
                                    masterDic[vendor][deviceId] = []
                                # Checking if we already have the switch,port tuple in the array
                                if (device['name'], port) not in masterDic[vendor][deviceId]:
                                    masterDic[vendor][deviceId].append((device['name'], port))
                                else:
                                    printv("(%s,%s) already exists for the mac %s for the vendor %s" %
                                           (device['name'], port, deviceId, vendor))
                            except:
                                printv("On switch %s port %s we could not get a vendor for the mac %s" %
                                       (device['name'], port, deviceId))
                                if deviceId not in masterDic['Unknown']:
                                    masterDic['Unknown'][deviceId] = []
                                if (device['name'], port) not in masterDic['Unknown'][deviceId]:
                                    masterDic['Unknown'][deviceId].append((device['name'], port))
                                else:
                                    printv("(%s,%s) already exists for the mac %s in the unknowns" %
                                           (device['name'], port, deviceId))
        else:
            printv("Skipping %s since there are no ports" % device['name'])

        return masterDic

    # The next place to look for a MAC is in the clients table
    def processDeviceClients(device, clients):

        # Getting our master dicts created
        masterDic = dict()
        masterDic['Unknown'] = dict()

        printv("Working with %s" % device['name'])
        printv("Checking clients on %s" % device['name'])

        # Now we check the clients on the switch using our rate limit function
        # clients = callAPI(device=device, clients=True, networkId=None, lldp=False)

        # Now we iterate through all the clients
        printv("Checking all %s clients on switch %s" % (len(clients), device['name']))

        for client in clients:
            '''
             'id': 'k6cfdd8', 
             'mac': '54:27:58:d0:27:8e', 
             'description': 'android-7e3242c6007b60f6', 
             'mdnsName': None, 'dhcpHostname': 
             'android-7e3242c6007b60f6', 
             'ip': '10.170.9.62', 
             'vlan': 270, 
             'switchport': '5', 
             'usage': {'sent': 56.0, 'recv': 213.0}}
            '''
            if 'mac' in client and bool(client['mac']):
                mac = formatMACAddr(client['mac'])

                # Seeing if we can get a vendor
                try:
                    vendor = maclookup().lookup(mac)
                    # Checking if we have a vendor dict
                    if vendor not in masterDic:
                        masterDic[vendor] = dict()
                    # Checking if we have a MAC array in the vendor
                    if mac not in masterDic[vendor]:
                        masterDic[vendor][mac] = []
                    # Checking if we already have the switch,port tuple in the array
                    if (device['name'], client['switchport']) not in masterDic[vendor][mac]:
                        masterDic[vendor][mac].append((device['name'], client['switchport']))
                    else:
                        printv("(%s,%s) already exists for the mac %s for the vendor %s" %
                               (device['name'], client['switchport'], mac, vendor))
                except:
                    printv("On switch %s port %s we could not get a vendor for the mac %s" %
                           (device['name'], client['switchport'], mac))
                    if mac not in masterDic['Unknown']:
                        masterDic['Unknown'][mac] = []
                    if (device['name'], client['switchport']) not in masterDic['Unknown'][mac]:
                        masterDic['Unknown'][mac].append((device['name'], client['switchport']))
                    else:
                        printv("(%s,%s) already exists for the mac %s in the unknowns" %
                               (device['name'], client['switchport'], mac))
        return masterDic

    # Now we go through and call the above inner functions
    start = str(int(time.time()))
    printv("Starting the thread pool at %s" % start)
    printi("Making API calls to gather required information")

    # We can have this many workers because our rate limit inner function will prevent us from hitting the max
    with futures.ThreadPoolExecutor(max_workers=100) as executor:
        devicePool = []
        for device in devices:
            # We put these sleep statements in to help reduce the number of back-offs needed
            printv("sending the device %s into the thread pool" % device['name'])
            # Getting our network id
            start = time.time()
            if 'networkId' in device:
                networkId = device['networkId']
            else:
                network = getDeviceNetwork(device['serial'], networks)
                networkId = network['id']
            finish = time.time()
            networkTime = finish - start
            printv("%s -> Get Network -> %f" % (device['name'], networkTime))
            start = time.time()
            ports = dashboard.devices.getNetworkDeviceLldp_cdp(networkId=networkId,
                                                               serial=device['serial'],
                                                               timespan=1296000)
            finish = time.time()
            networkTime = finish - start
            printv("%s -> Get Ports -> %f" % (device['name'], networkTime))
            devicePool.append(executor.submit(processDeviceLLDP, device, ports, networkId))
            start = time.time()
            clients = dashboard.clients.getDeviceClients(serial=device['serial'], timespan=1296000)
            finish = time.time()
            networkTime = finish - start
            printv("%s -> Get Ports -> %f" % (device['name'], networkTime))
            devicePool.append(executor.submit(processDeviceClients, device, clients))

        printv("Now we are waiting for the threads to complete")
        printi("Finished making API calls")
        printi("Processing returned data")
        complete_futures, incomplete_futures = futures.wait(devicePool)
        finish = str(int(time.time()))
        printv("All jobs have finished at %s" % finish)
        printv("Time to complete %s" % str(int(start) - int(finish)))
        printv("Now getting all the results from the complete pool")
        # The time that we save using multithreading makes this mess totally worth it
        completeMasterDic = dict()
        for complete in complete_futures:
            for key in complete.result().keys():
                # If the Vendor is not already in the master dict then we add it in and then go through the macs
                if key not in completeMasterDic:
                    completeMasterDic[key] = dict()
                    # Now we go through the macs in the vendor
                for macs in complete.result()[key]:
                    # If the vendor does not have this mac address then we add it in
                    if macs not in completeMasterDic[key]:
                        completeMasterDic[key][macs] = []
                    # Now we go through the mac and add any non duplicate tuples
                    for deviceTuple in complete.result()[key][macs]:
                        # If the tuple is not in the array then we add it in
                        if deviceTuple not in completeMasterDic[key][macs]:
                            completeMasterDic[key][macs].append(deviceTuple)
                        else:
                            printv("%s was a duplicate tuple for %s->%s" % (str(deviceTuple), key, macs))

        # In theory this should never run but I am leaving it here just in case
        if len(incomplete_futures) > 0:
            printv("Something did not get a chance to complete and that is bad")
            printv("Not sure what you can do about that though so I guess you can ignore this error?")
            for incomplete in incomplete_futures:
                printv(incomplete.result())

    # For testing purposes, we will print the newly made dict and then return it
    printv(json.dumps(completeMasterDic, indent=4))
    return completeMasterDic


# Will list out any LLDP/CDP information for any amount of switches
# It will also try to map any MACs to Vendors for extra information
def getLLDPCDPInfo(dashboard, devices, networks):
    '''
    See notes on the gatherMACS function as to why this was removed

    # The api only allows us 5 calls per second
    # By having this limiter and exponential back-off, we can maximize speed without worry
    @on_exception(expo, RateLimitException, max_tries=10)
    @limits(calls=5, period=3)
    def callAPI(device, networkId):
        print("%s is making a thread call" % device['name'])
        return dashboard.devices.getNetworkDeviceLldp_cdp(networkId=networkId,
                                                          serial=device['serial'],
                                                          timespan=1296000)
    '''

    def getInfo(device, ports):

        data = []

        printv("working with %s" % device['name'])

        # If we ports is an empty dict then we just move on to the next device
        if not bool(ports):
            return []

        for port in ports['ports']:
            # LLDP
            if 'lldp' in ports['ports'][port]:
                # Getting the system name
                if 'systemName' in ports['ports'][port]['lldp']:
                    deviceName = ports['ports'][port]['lldp']['systemName']
                    if "MR42" not in deviceName:
                        # Removes the first bit and only gives us the switch name
                        # ex Meraki MS425-32 - WDCB125SW01 => WDCB125SW01
                        if 'Meraki' in str(ports['ports'][port]['lldp']['systemName']).split(" - ", 1)[0]:
                            deviceName = str(ports['ports'][port]['lldp']['systemName']).split(" - ", 1)[1]
                        else:
                            deviceName = str(ports['ports'][port]['lldp']['systemName']).split(" - ", 1)[0]
                    else:
                        printv("Wireless Device \"%s\" skipped" % deviceName)
                        continue
                elif 'portId' in ports['ports'][port]['lldp'] and bool(ports['ports'][port]['lldp']['portId']):
                    portID = str(ports['ports'][port]['lldp']['portId']).replace(':', '')
                    if len(portID) == 12:
                        try:
                            deviceName = maclookup().lookup(ports['ports'][port]['lldp']['portId'])
                        except:
                            deviceName = "N/A"
                    else:
                        deviceName = "N/A"
                else:
                    deviceName = "N/A"
                # Getting MAC
                if 'portId' in ports['ports'][port]['lldp'] and bool(ports['ports'][port]['lldp']['portId']):
                    destport = ports['ports'][port]['lldp']['portId']
                    if len(str(destport).replace(':', '')) == 12:
                        try:
                            vendor = maclookup().lookup(destport)
                            destport = "%s (%s)" % (destport, vendor)
                        except:
                            printv("Couldnt get a vendor for the mac %s" % destport)
                else:
                    destport = "N/A"
                # Getting IP
                if 'managementAddress' in ports['ports'][port]['lldp'] and \
                        bool(ports['ports'][port]['lldp']['managementAddress']):
                    destip = ports['ports'][port]['lldp']['managementAddress']
                else:
                    destip = "N/A"
            # CDP
            elif 'cdp' in ports['ports'][port]:
                if 'deviceId' in ports['ports'][port]['cdp']:
                    portID = str(ports['ports'][port]['cdp']['portId']).replace(':', '')
                    if len(portID) == 12:
                        try:
                            deviceName = maclookup().lookup(ports['ports'][port]['cdp']['portId'])
                        except:
                            deviceName = "N/A"
                    else:
                        deviceName = "N/A"
                else:
                    deviceName = "N/A"
                if 'address' in ports['ports'][port]['cdp'] and bool(ports['ports'][port]['cdp']['address']):
                    destip = ports['ports'][port]['cdp']['address']
                    if not bool(destip):
                        destip = "N/A"
                else:
                    destip = "N/A"
                if 'portId' in ports['ports'][port]['cdp'] and bool(ports['ports'][port]['cdp']['portId']):
                    destport = ports['ports'][port]['cdp']['portId']
                    if len(str(destport).replace(':', '')) == 12:
                        try:
                            vendor = maclookup().lookup(destport)
                            destport = "%s (%s)" % (destport, vendor)
                        except:
                            printv("Couldnt get a vendor for the mac %s" % destport)
                else:
                    destport = "N/A"
            else:
                continue
            # Lastly we check if port can be an int to help with our sort
            if is_int(port):
                port = int(port)
            data.append([device['name'],
                         port,
                         deviceName,
                         destport,
                         destip
                         ])

        return data

    # Now we go through and call the above inner functions
    start = str(int(time.time()))
    printv("Starting the thread pool at %s" % start)
    if type(devices) is not list:
        printv("Single device sent in")
        devices = [devices]

    with futures.ThreadPoolExecutor(max_workers=50) as executor:
        devicePool = []
        for device in devices:
            # We put these sleep statements in to help reduce the number of back-offs needed
            printv("sending the device %s into the thread pool" % device['name'])
            # Getting our network id
            start = time.time()
            if 'networkId' in device:
                networkId = device['networkId']
            else:
                network = getDeviceNetwork(device['serial'], networks)
                networkId = network['id']
            finish = time.time()
            networkTime = finish - start
            printv("%s -> Get Network -> %f" % (device['name'], networkTime))
            start = time.time()
            ports = dashboard.devices.getNetworkDeviceLldp_cdp(networkId=networkId,
                                                               serial=device['serial'],
                                                               timespan=1296000)
            finish = time.time()
            networkTime = finish - start
            printv("%s -> Get Ports -> %f" % (device['name'], networkTime))
            devicePool.append(executor.submit(getInfo, device, ports))

    printv("Now we are waiting for the threads to complete")
    complete_futures, incomplete_futures = futures.wait(devicePool)
    finish = str(int(time.time()))
    printv("All jobs have finished at %s" % finish)
    printv("Time to complete %s" % str(int(finish) - int(start)))
    printv("Now getting all the results from the complete pool")

    masterData = []
    for complete in complete_futures:
        for data in complete.result():
            if data is not []:
                masterData.append(data)

    # Not going to lie here, I fell asleep during my CMSC330 Lambda lecture so I needed stack overflow
    # https://stackoverflow.com/questions/6666748/python-sort-list-of-lists-ascending-and-then-decending
    masterData.sort(key=lambda x: (x[0], x[1]))
    masterData.insert(0, ["S-Switch", "S-Port", "D-Switch", "D-Port", "D-IP"])
    printi(tabulate(masterData, headers='firstrow'))
    printi("\n")


# WIP.  Goal: Change the wifi password across all sites and update accordingly
# Wifi password should be [word][number and symbols randomized of len 1-3]x2
# ssids = dashboard.ssids.getNetworkSsid(networkId=netid,number=1)
def updateWifiPassword(dashboard):
    return None


# Gathers all the port information on a device(s)
def getSwitchPortCSV(dashboard, devices):
    portData = dict()
    filter = ['number', 'name', 'tags', 'enabled', 'poeEnabled', 'type', 'vlan',
              'voiceVlan', 'allowedVlans', 'rstpEnabled', 'stpGuard']
    p = dict()
    tmp = []
    for device in devices:
        for port in dashboard.switch_ports.getDeviceSwitchPorts(serial=device['serial']):
            p = dict()
            for k, v in port.items():
                if k not in filter:
                    continue
                if v is None:
                    p[k] = ''
                else:
                    p[k] = v
            tmp.append(p)
        portData[device['name']] = tmp
        tmp = []
    return portData


# Traces a source and destination IP through the ACL-es on the MS and then through the Firewall on MX
def tracePacketInACL(src, dst, aclList):
    printv("Checking against current ruleset")
    data = [['#', 'Comment', 'Policy', 'Source', 'Destination', 'Impact']]
    for acl in aclList:

        if 'MX-01' in acl['#']:
            data.append([
                '-' * len(data[5][0]),
                '-' * len(data[5][1]),
                '-' * len(data[5][2]),
                '-' * len(data[5][3]),
                '-' * len(data[5][4]),
                '-' * len(data[5][5])
            ])

        impact = 'None'
        defaultRule = False

        # Checking ACL
        if any(network for network in acl['srcCidr'] if src in network):
            printv("Passed in source impacted by rule %s" % acl['#'])
            if any(network for network in acl['dstCidr'] if dst in network):
                printv("Passed in destination impacted by rule %s" % acl['#'])
                if 'allow' in acl['policy']:
                    printv("Policy for rule %s is allow" % acl['#'])
                    if 'Default rule' in acl['comment']:
                        printv("Hit the default rule and thus going to continue")
                        defaultRule = True
                    impact = 'Allowed'
                else:
                    printv("Policy for rule %s is deny" % acl['#'])
                    impact = 'Denied'

        data.append([
            acl['#'],
            acl['comment'],
            acl['policy'],
            ",".join([str(network) for network in acl['srcCidr']][:3]),
            ",".join([str(network) for network in acl['dstCidr']][:3]),
            impact
        ])
        if 'None' not in impact and not defaultRule:
            break

    printi(tabulate(data, headers='firstrow'))


# Gathers up the ACL/Firewall rules and formats them in a user friendly way
def getACLS(networkId):
    # MS ACLs
    msACL = []
    printv("Gathering ACL rules on the MS switches")
    for x, acl in enumerate(dashboard.switch_acls.getNetworkSwitchAccessControlLists(networkId)['rules'][:-1]):
        # Cleaning up the dict and formatting it accordingly
        tmp = {}
        tmp['#'] = "MS-" + str(x + 1).zfill(2)
        tmp['comment'] = acl['comment']
        tmp['policy'] = acl['policy']
        # Formatting values
        if 'any' in acl['srcCidr'].lower():
            tmp['srcCidr'] = [IPNetwork('0.0.0.0/0')]
        else:
            tmp['srcCidr'] = [IPNetwork(network) for network in acl['srcCidr'].split(",")]
        if 'any' in acl['dstCidr'].lower():
            tmp['dstCidr'] = [IPNetwork('0.0.0.0/0')]
        else:
            tmp['dstCidr'] = [IPNetwork(network) for network in acl['dstCidr'].split(",")]
        msACL.append(tmp)
    # MX Firewall
    mxACL = []
    printv("Gathering Firewalls rules on the MX appliances")
    try:
        for x, acl in enumerate(dashboard.mx_l3_firewall.getNetworkL3FirewallRules(networkId)[:-1]):
            # Cleaning up the dict and formatting it accordingly
            tmp = {}
            tmp['#'] = "MX-" + str(x + 1).zfill(2)
            tmp['comment'] = acl['comment']
            tmp['policy'] = acl['policy']
            # Formatting values
            if 'any' in acl['srcCidr'].lower():
                tmp['srcCidr'] = [IPNetwork('0.0.0.0/0')]
            else:
                tmp['srcCidr'] = [IPNetwork(network) for network in acl['srcCidr'].split(",")]
            if 'any' in acl['destCidr'].lower():
                tmp['dstCidr'] = [IPNetwork('0.0.0.0/0')]
            else:
                tmp['dstCidr'] = [IPNetwork(network) for network in acl['destCidr'].split(",")]
            mxACL.append(tmp)
    except mer.exceptions.APIError as e:
        printv("meraki.exceptions.APIError: MX L3 firewall, getNetworkL3FirewallRules - 4prompt Not Found")
        printi("This network does not have an MX appliance")
        mxACL = None
    return msACL, mxACL


# Allows a user to enter either an ip or fqdn and get a formatted ip as the return
def getAddress():
    while True:
        subSubChoice = input(prompt)
        if subSubChoice == '0':
            return '0'
        address = None
        # Input validation for source
        if subSubChoice.lower() != 'any' and not is_ip(subSubChoice.strip()):
            printv("Detected name attempting DNS")
            hostname = subSubChoice.split(".")[0]
            try:
                addr = socket.gethostbyname(hostname)
                address = IPNetwork(addr + '/32')
                return address
            except:
                printv("Unable to get an address for: %s" % hostname)
                printi("%s not in DNS" % hostname)
        if '/' in subSubChoice:
            try:
                address = IPNetwork(subSubChoice)
            except AddrFormatError:
                printv("Invalid address provided: %s" % subSubChoice)
                printi("Invalid address")
        elif 'any' in subSubChoice.lower():
            address = IPNetwork('0.0.0.0/0')
        else:
            try:
                address = IPNetwork(subSubChoice + '/32')
            except AddrFormatError:
                printv("Invalid address provided: %s" % subSubChoice)
                printi("Invalid address")
        if address is not None:
            return address


# Adds an ACL/Firewall rule in at the specified position
def insertACL(position, aclList):
    # Making the new ACL
    while True:
        printi("Policy:")
        policy = input(prompt).lower()
        if 'allow' in policy or 'deny' in policy:
            break
        else:
            printi("Please specify either allow or deny")
    printi("Comment:")
    comment = input(prompt)
    printi("Source:")
    printi("Ex. any or 192.168.1.1 or 10.160.34.0/24")
    source = [getAddress()]
    printi("Destination:")
    printi("Ex. any or 192.168.1.1 or 10.160.34.0/24")
    destination = [getAddress()]
    newACL = dict()
    # If the user is trying to put it at the beginning of the list
    spot = int(position.split("-")[1])
    if spot == 0:
        newACL['#'] = position.split("-")[0] + '-01'
    else:
        newACL['#'] = position
    newACL['comment'] = comment
    newACL['policy'] = policy
    newACL['srcCidr'] = source
    newACL['dstCidr'] = destination

    if spot != 0:
        index = spot - 1
    else:
        index = 0
    newACLList = []

    # In case the ACL list has no entries
    if len(aclList) == 0:
        printv("Empty rule list detected. Putting rule at the beginning")
        newACL['#'] = position.split("-")[0] + '-01'
        newACLList.append(newACL)
        printi("New ACL inserted into list")
        return newACLList

    for x, acl in enumerate(aclList):
        if x < index:
            newACLList.append(acl)
        if x == index:
            newACLList.append(newACL)
            if acl['#'].split("-")[1][0] == '0':
                newPos = acl['#'].split("-")[0] + "-" + str(int(acl['#'].split("-")[1][1]) + 1).zfill(2)
            else:
                newPos = acl['#'].split("-")[0] + "-" + str(int(acl['#'].split("-")[1]) + 1).zfill(2)
            newACLList.append({
                '#': newPos,
                'comment': acl['comment'],
                'policy': acl['policy'],
                'srcCidr': acl['srcCidr'],
                'dstCidr': acl['dstCidr']
            })
        if x > index:
            if acl['#'].split("-")[1][0] == '0':
                newPos = acl['#'].split("-")[0] + "-" + str(int(acl['#'].split("-")[1][1]) + 1).zfill(2)
            else:
                newPos = acl['#'].split("-")[0] + "-" + str(int(acl['#'].split("-")[1]) + 1).zfill(2)
            newACLList.append({
                '#': newPos,
                'comment': acl['comment'],
                'policy': acl['policy'],
                'srcCidr': acl['srcCidr'],
                'dstCidr': acl['dstCidr']
            })

    printi("New ACL inserted into list")
    return newACLList


# Prints out the current ACL/Firewall list
def printACLS(aclList):
    data = [['#', 'Comment', 'Policy', 'Source', 'Destination']]
    for acl in aclList:
        data.append([
            acl['#'],
            acl['comment'],
            acl['policy'],
            ",".join([str(network) for network in acl['srcCidr']][:3]),
            ",".join([str(network) for network in acl['dstCidr']][:3])
        ])
    # Adding the default rule at the bottom
    data.append([
        '',
        'Default rule',
        'Allow',
        'Any',
        'Any'
    ])
    printi(tabulate(data, headers='firstrow'))


# Deletes an ACL/Firewall rule in a given position
def deleteACL(positions, msACL, mxACL):
    newMSACL = []
    newMXACL = []

    # Checking to see if we are being asked to delete more than one rule
    range = re.search('(M[S|X]-\d\d)-(M[S|X]-\d\d)', positions.upper())

    if range is None:
        if re.search('M(S|X)-\d\d', positions.upper()) is None:
            printi("Invalid input given")
            return
        else:
            # Deleting single ACL
            if mxACL is None and position.upper().split("-")[0] == 'MX':
                printi("Invalid input given")
            elif mxACL is not None and position.upper().split("-")[0] == 'MX':
                mxX = int(position.split("-")[1])
                mxY = int(mxX)
                counter = 1
                for i, acl in enumerate(mxACL):
                    if mxX <= i <= mxY:
                        continue
                    else:
                        newPos = "MX-" + str(counter).zfill(2)
                        counter += 1
                        newMXACL.append({
                            '#': newPos,
                            'comment': acl['comment'],
                            'policy': acl['policy'],
                            'srcCidr': acl['srcCidr'],
                            'dstCidr': acl['dstCidr']
                        })
                # return condition for MX->MX
                return None, newMXACL
            elif position.upper().split("-")[0] == 'MS':
                msX = int(position.split("-")[1])
                msY = int(msX)
                counter = 1
                for i, acl in enumerate(msACL):
                    if msX <= i <= msY:
                        continue
                    else:
                        newPos = "MS-" + str(counter).zfill(2)
                        counter += 1
                        newMSACL.append({
                            '#': newPos,
                            'comment': acl['comment'],
                            'policy': acl['policy'],
                            'srcCidr': acl['srcCidr'],
                            'dstCidr': acl['dstCidr']
                        })
                return newMSACL, None
    else:
        # Deleting a range of ACL-es
        start = range.group(1)
        end = range.group(2)
        msX, msY, mxX, mxY = None, None, None, None

        # Our cases are MS->MS, MS->MX, and MX->MX
        if 'MS' in start:
            # These take care of our first two cases
            msX = int(start.split("-")[1]) - 1
            if 'MX' in end and mxACL is None:
                printi("Invalid range given")
                return
            elif 'MX' in end and mxACL is not None:
                # We cant delete the default allow all so we exempt it here
                msY = len(msACL) - 1
                mxX = 0
                mxY = int(end.split("-")[1]) - 1
            else:
                msY = int(end.split("-")[1]) - 1

            # Now that we have our ranges we can make our new ACL list
            counter = 1
            for i, acl in enumerate(msACL):
                if msX <= i <= msY:
                    continue
                else:
                    newPos = "MS-" + str(counter).zfill(2)
                    counter += 1
                    newMSACL.append({
                        '#': newPos,
                        'comment': acl['comment'],
                        'policy': acl['policy'],
                        'srcCidr': acl['srcCidr'],
                        'dstCidr': acl['dstCidr']
                    })
            if mxY is not None:
                counter = 1
                for i, acl in enumerate(mxACL):
                    if mxX <= i <= mxY:
                        continue
                    else:
                        newPos = "MX-" + str(counter).zfill(2)
                        counter += 1
                        newMXACL.append({
                            '#': newPos,
                            'comment': acl['comment'],
                            'policy': acl['policy'],
                            'srcCidr': acl['srcCidr'],
                            'dstCidr': acl['dstCidr']
                        })
                # return condition for MS->MX
                return newMSACL, newMXACL
            else:
                # return condition for MS->MS
                return newMSACL, None
        else:
            # In this case it can only be MX to MX and if it is not then we throw an error
            mxX = int(start.split("-")[1]) - 1
            if 'MS' in end:
                printi("Invalid destination.  If start is MX then end must be too")
                return
            else:
                mxY = int(end.split("-")[1]) - 1
                counter = 1
                for i, acl in enumerate(mxACL):
                    if mxX <= i <= mxY:
                        continue
                    else:
                        newPos = "MX-" + str(counter).zfill(2)
                        counter += 1
                        newMXACL.append({
                            '#': newPos,
                            'comment': acl['comment'],
                            'policy': acl['policy'],
                            'srcCidr': acl['srcCidr'],
                            'dstCidr': acl['dstCidr']
                        })
                # return condition for MX->MX
                return None, newMXACL


# Will allow you to compare your current ACL changes against a previous version
def compareACLs(newACL, oldACL):
    count = 0
    oldACLLength = len(oldACL)
    printv("Old length %d" % oldACLLength)
    aclData = [['Diff', '#', 'Comment', 'Policy', 'Source', 'Destination']]
    for acl in newACL:
        if count < oldACLLength:
            if acl != oldACL[count]:
                aclData.append([
                    colored('---', 'red'),
                    oldACL[count]['#'],
                    oldACL[count]['comment'],
                    oldACL[count]['policy'],
                    ",".join([str(network) for network in oldACL[count]['srcCidr']][:3]),
                    ",".join([str(network) for network in oldACL[count]['dstCidr']][:3]),
                ])
                aclData.append([
                    colored('+++', 'green'),
                    acl['#'],
                    acl['comment'],
                    acl['policy'],
                    ",".join([str(network) for network in acl['srcCidr']][:3]),
                    ",".join([str(network) for network in acl['dstCidr']][:3]),
                ])
                aclData.append([
                    ' ' * 4,
                    ' ' * 4,
                    ' ' * 4,
                    ' ' * 4,
                    ' ' * 4,
                    ' ' * 4
                ])
            else:
                aclData.append([
                    ' ' * 4,
                    acl['#'],
                    acl['comment'],
                    acl['policy'],
                    ",".join([str(network) for network in acl['srcCidr']][:3]),
                    ",".join([str(network) for network in acl['dstCidr']][:3]),
                ])
        else:
            aclData.append([
                colored('+++', 'green'),
                acl['#'],
                acl['comment'],
                acl['policy'],
                ",".join([str(network) for network in acl['srcCidr']][:3]),
                ",".join([str(network) for network in acl['dstCidr']][:3]),
            ])
        count += 1
    # If we trimmed stuff off of the bottom this conditional will catch it and ensure it is seen as a change
    if count <= oldACLLength:
        for acl in oldACL[count:]:
            aclData.append([
                colored('---', 'red'),
                acl['#'],
                acl['comment'],
                acl['policy'],
                ",".join([str(network) for network in acl['srcCidr']][:3]),
                ",".join([str(network) for network in acl['dstCidr']][:3]),
            ])

    printi(tabulate(aclData, headers='firstrow'))


# Pushes your current changes to production
def commitACLs(dashboard, networkId, msACL, mxACL):
    # return
    # First thing we need to do is reformat our ACL lists back into the way they came
    printv("Committing ACL changes")
    msACLFormatted = []
    for acl in msACL:
        msACLFormatted.append({
            'policy': acl['policy'],
            "ipVersion": "ipv4",
            "protocol": "any",
            'srcCidr': ",".join([str(network) for network in acl['srcCidr']]),
            "srcPort": "any",
            'dstCidr': ",".join([str(network) for network in acl['dstCidr']]),
            "dstPort": "any",
            "vlan": "any",
            'comment': acl['comment']
        })
    printi("MS ACLs")
    msACLTemp = [['comment', 'ipVersion', 'protocol', 'srcCidr', 'srcPort', 'dstCidr', 'dstPort', 'vlan', 'comment']] + \
                [x for x in [list(dic.values()) for dic in msACLFormatted]]
    printi(tabulate(msACLTemp, headers='firstrow'))
    if mxACL is not None:
        mxACLFormatted = []
        for acl in mxACL:
            mxACLFormatted.append({
                'policy': acl['policy'],
                "protocol": "any",
                'srcCidr': ",".join([str(network) for network in acl['srcCidr']]),
                "srcPort": "any",
                'destCidr': ",".join([str(network) for network in acl['dstCidr']]),
                "destPort": "any",
                'comment': acl['comment'],
                "syslogEnabled": False
            })
        printi("MX ACLs")
        mxACLTemp = [['policy', 'protocol', 'srcCidr', 'srcPort', 'destCidr', 'destPort', 'comment', 'syslogEnabled'],
                     [list(dic.values()) for dic in mxACLFormatted]]
        printi(tabulate(mxACLTemp, headers='firstrow'))
    printi("Please double and triple check the above information and ensure it is correct")
    printi("If the above information is correct, type YES to continue")
    subchoice = input(prompt).upper()
    if subchoice != 'YES':
        printi("Aborting")
        return -1
    else:
        printi("Committing MS Changes")
        printv("ACL/FIREWALL RULES ARE BEING CHANGED")
        printv("Original MS Rules")
        try:
            printv(json.dumps(dashboard.switch_acls.getNetworkSwitchAccessControlLists(networkId)))
        except:
            printv("No MS Rules")
        printv("Original MX Rules")
        try:
            printv(json.dumps(dashboard.mx_l3_firewall.getNetworkL3FirewallRules(networkId)))
        except:
            printv("No MX Rules")
        printv("Clearing the ACLs")
        dashboard.switch_acls.updateNetworkSwitchAccessControlLists(networkId, [])
        printv("ACL-es cleared")
        dashboard.switch_acls.updateNetworkSwitchAccessControlLists(networkId, msACLFormatted)
        printi("ACL-es have been updated")
        if mxACL is not None:
            printi("Confirm this worked and then hit enter to continue")
            input(prompt)
            printi("Committing MX Changes")
            dashboard.mx_l3_firewall.updateNetworkL3FirewallRules(networkId, mxACLFormatted)
        printi("Changes are in place")
        return 0


# Filters out LAGGs by regex
def filterAggs(aggs, filter):
    aggArr = []
    for agg in aggs:
        for port in agg['switchPorts']:
            if re.match(filter, port['serial']):
                aggArr.append(agg)
    return aggArr


# Fetches all the LAGGs in the current device set
def getAggs(dashboard, devices, networkId):
    formatedAggs = []
    originalAggs = None
    try:
        originalAggs = dashboard.link_aggregations.getNetworkSwitchLinkAggregations(networkId)
    except:
        printi("LAGG is only supported in MS networks")
        return None
    for agg in originalAggs:
        tmp = dict()
        tmp['id'] = agg['id']
        tmparr = []
        for port in agg['switchPorts']:
            tmparr.append({'serial': serialToSwitch(port['serial'], devices), 'portId': port['portId']})
        tmp['switchPorts'] = tmparr
        formatedAggs.append(tmp)
    return (originalAggs, formatedAggs)


# Converts a serial to switch
def serialToSwitch(serial, devices):
    for device in devices:
        if serial.lower() in device['serial'].lower():
            return device['name']
    return None


# Prints out the LAGG groups
def printAggs(aggs):
    data = []
    for agg in aggs:
        group = ''
        groupLen = len(agg['switchPorts'])
        for x, port in enumerate(agg['switchPorts']):
            group += port['serial'] + " Port " + port['portId']
            if (x + 1) != groupLen:
                group += " <=> "
        data.append([
            agg['id'],
            group
        ])
    data.insert(0, ['ID', 'Group'])
    printi(tabulate(data, headers='firstrow'))


'''               '''
### SCRIPT RUNNER ###
'''               '''
if __name__ == "__main__":

    print("Enter API Key")
    apikey = input("=> ").strip()
    networkFilter = [['test']]
    printv("Network filter set to %s" % ','.join(networkFilter[0]))
    # By default we want to filter out MX and MR since they have different api calls
    deviceFilter = [["MR", "MX"]]
    for x, filter in enumerate(deviceFilter):
        printv("%d: %s" % (x, ','.join(filter)))
    printv("Starting our API calls by creating a dashboard instance")
    dashboard, found = getDashboard(apikey=apikey, maxRetry=3)
    while not found:
        print("Invalid API Key")
        apikey = input("=> ").strip()
        dashboard, found = getDashboard(apikey=apikey, maxRetry=3)

    printv("Getting our organization information")
    organizations = dashboard.organizations.getOrganizations()
    orgID = organizations[0]['id']

    colors = ['red', 'yellow', 'green', 'cyan', 'blue', 'magenta'] * 5
    title = ''.join(colored(y, colors[x]) for x, y in enumerate('Meraki API Toolbox'))

    networks = None
    devices = None
    macDict = dict()
    switchVlans = dict()
    switchPorts = dict()
    aggDict = None

    '''              '''
    ### PROGRAM LOOP ###
    '''              '''
    while True:

        print("\n     " + title)
        print("01. Find Switch")
        print("02. Get Switch Port Usage Stats")
        print("03. Get Switch LLDP Information")
        print("04. Print All Devices")
        print("05. Copy Switch Port Configuration")
        print("06. Locate MACs or Vendors")
        print("07. Get Switch VLANs")
        print("08. List All Port Information")
        print("09. Manage ACL and Firewall Rules")
        print("10. Print Link Aggregation Groups")
        print("11. Set Variables")
        print("12. Save Data to File")
        # print("13. Change WiFi Password")
        # print("14. Enable Read Only Mode")
        # print("15. Load all data")
        print("00. Exit")
        choice = input("=> ")

        '''         '''
        ### EXITING ###
        '''         '''
        if choice == "0" or choice == "00":
            printv("Script exiting")
            printi("Have a wonderful day")
            LOGFILE.close()
            exit(0)

        '''             '''
        ### FIND SWITCH ###
        '''             '''
        if choice == "1":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            prompt = "=(01)> "
            while True:
                # Will look for a switch with a matching IP, Serial, or Name
                printi("Provide Serial, IP, or Name. 0 to go back")
                filter = input(prompt)
                if filter == "0":
                    break
                else:
                    # Passing this off to a utility function to reduce code here and to allow us to re-use this logic
                    device, found = is_device(devices, filter)
                    if found:
                        INDENT += 1
                        printDevices(device, 1)
                        INDENT -= 1
                    else:
                        printi("Could not find that device")

        '''                             '''
        ### GET SWITCH PORT USAGE STATS ###
        '''                             '''
        if choice == "2":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            printi("Please wait as this may take a while...")
            INDENT += 1
            getPortUsageStats(dashboard=dashboard, devices=devices)
            INDENT -= 1

        '''                   '''
        ### GET CDP/LLDP INFO ###
        '''                   '''
        if choice == "3":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            prompt = "=(03)> "
            while True:
                printi("1. Provide Serial, IP, or Name")
                printi("2. Print All Devices LLDP/CDP Information")
                printi("0. Go Back")
                subChoice = input(prompt).strip()
                INDENT += 1
                if subChoice == "1":
                    filter = input(prompt).strip()
                    device, found = is_device(devices, filter)
                    while not found:
                        printi("Device not found")
                        subChoice = input(prompt).strip()
                        device, found = is_device(devices, filter)
                    getLLDPCDPInfo(dashboard=dashboard, devices=device, networks=networks)
                    continue
                if subChoice == "2":
                    printi("Please wait as this may take a while...")
                    getLLDPCDPInfo(dashboard=dashboard, devices=devices, networks=networks)
                    continue
                if subChoice == "0":
                    INDENT -= 1
                    break
                INDENT -= 1

        '''                   '''
        ### PRINT ALL DEVICES ###
        '''                   '''
        if choice == "4":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            INDENT += 1
            printDevices(devices=devices, columns=5, detailed=True)
            INDENT -= 1

        '''                                '''
        ### COPY SWITCH PORT CONFIGURATION ###
        '''                                '''
        if choice == "5":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)

            prompt = "=(05)> "
            printi("1. Default Input")
            printi("2. CSV Input")
            printi("3. CSV File")
            printi("0. Go back")
            subChoice = input(prompt)

            INDENT += 1
            while subChoice != "0":
                if subChoice == "1":
                    # Source Switch
                    printi("Enter source switch Name, Serial, or IP")
                    filter = input(prompt)
                    sourceSwitch, found = is_device(devices, filter)
                    while not found:
                        printi("Could not find that device. Try again or 0 to go back")
                        filter = input(prompt)
                        if filter == "0":
                            break
                        sourceSwitch, found = is_device(devices, filter)
                    if filter == "0":
                        INDENT -= 1
                        continue
                    # Source Port
                    printi("Enter source switch port number")
                    filter = input(prompt)
                    sourcePort, found = is_port(dashboard=dashboard, device=sourceSwitch, filter=filter)
                    while not found:
                        printi("Could not find that port. Try again or 0 to go back")
                        filter = input(prompt)
                        if filter == "0":
                            break
                        sourcePort, found = is_port(dashboard=dashboard, device=sourceSwitch, filter=filter)
                    if filter == "0":
                        INDENT -= 1
                        continue

                    # Destination Switch
                    printi("Enter destination switch Name, Serial, or IP")
                    filter = input(prompt)
                    destSwitch, found = is_device(devices, filter)
                    while not found:
                        printi("Could not find that device. Try again or 0 to go back")
                        filter = input(prompt)
                        if filter == "0":
                            break
                        destSwitch, found = is_device(devices, filter)
                    if filter == "0":
                        INDENT -= 1
                        continue
                    # Destination Port
                    printi("Enter destination switch port number")
                    filter = input(prompt)
                    destPort, found = is_port(dashboard=dashboard, device=sourceSwitch, filter=filter)
                    while not found:
                        printi("Could not find that device. Try again or 0 to go back")
                        filter = input(prompt)
                        if filter == "0":
                            break
                        destPort, found = is_port(dashboard=dashboard, device=sourceSwitch, filter=filter)
                    if filter == "0":
                        INDENT -= 1
                        continue

                    # Confirm information with user before proceeding
                    printi("Copying the port configuration from %s - %s to %s - %s" %
                           (sourceSwitch['name'], sourcePort['number'], destSwitch['name'], destPort['number']))
                    printi("If the above is correct hit enter else 0 to go back")
                    check = input(prompt)
                    if check == "0":
                        INDENT -= 1
                        continue
                    else:
                        copySwitchPortConfig(dashboard=dashboard,
                                             sSwitch=sourceSwitch,
                                             sPort=sourcePort,
                                             dSwitch=destSwitch,
                                             dPort=destPort)
                elif subChoice == "2":
                    while True:
                        printi("Enter CSV Info or 0 to go back")
                        filter = ''
                        found = True
                        csvInput = input(prompt)
                        if csvInput == "0":
                            break
                        # Source Switch
                        sourceSwitch, foundsS = is_device(devices, csvInput.split(",")[0].strip())
                        # Source Port
                        sourcePort, foundsP = is_port(dashboard=dashboard, device=sourceSwitch,
                                                      filter=csvInput.split(",")[1].strip())
                        # Destination Switch
                        destSwitch, founddS = is_device(devices, csvInput.split(",")[2].strip())
                        # Destination Port
                        destPort, founddP = is_port(dashboard=dashboard, device=sourceSwitch,
                                                    filter=csvInput.split(",")[3].strip())
                        if not (foundsS and foundsP and founddS and founddP):
                            printi("Invalid input provided")
                            continue
                        # Confirm information with user before proceeding
                        printi("Copying the port configuration from %s - %s to %s - %s" %
                               (sourceSwitch['name'], sourcePort['number'], destSwitch['name'], destPort['number']))
                        printi("If the above is correct hit enter else 0 to go back")
                        check = input(prompt)
                        if check == "0":
                            INDENT -= 1
                            continue
                        else:
                            copySwitchPortConfig(dashboard=dashboard,
                                                 sSwitch=sourceSwitch,
                                                 sPort=sourcePort,
                                                 dSwitch=destSwitch,
                                                 dPort=destPort)
                elif subChoice == "3":
                    printi("Provide name of CSV file or 0 to go back")
                    csvFile = input(prompt)
                    if csvFile == "0":
                        break
                    try:
                        with open(csvFile) as f:
                            csvInput = f.readline().strip()
                            count = 1
                            csvInputs = []
                            while csvInput:
                                printv(csvInput)
                                # Source Switch
                                sourceSwitch, foundsS = is_device(devices, csvInput.split(",")[0].strip())
                                # Source Port
                                sourcePort, foundsP = is_port(dashboard=dashboard, device=sourceSwitch,
                                                              filter=csvInput.split(",")[1].strip())
                                # Destination Switch
                                destSwitch, founddS = is_device(devices, csvInput.split(",")[2].strip())
                                # Destination Port
                                destPort, founddP = is_port(dashboard=dashboard, device=sourceSwitch,
                                                            filter=csvInput.split(",")[3].strip())
                                if not (foundsS and foundsP and founddS and founddP):
                                    printi("Invalid input provided on line %d" % count)
                                    printi("Hit enter to ignore this line or 0 to break")
                                    subSubChoice = input(prompt)
                                    if subSubChoice == '0':
                                        break
                                    else:
                                        csvInput = f.readline().strip()
                                        continue
                                csvInputs.append(
                                    [
                                        sourceSwitch,
                                        sourcePort,
                                        destSwitch,
                                        destPort
                                    ]
                                )
                                csvInput = f.readline().strip()
                            f.close()
                            for change in csvInputs:
                                # Confirm information with user before proceeding
                                printi("Copying the port configuration from %s - %s to %s - %s" %
                                       (change[0]['name'], change[1]['number'], change[2]['name'], change[3]['number']))
                                copySwitchPortConfig(dashboard=dashboard,
                                                     sSwitch=change[0],
                                                     sPort=change[1],
                                                     dSwitch=change[2],
                                                     dPort=change[3])
                    except FileNotFoundError as e:
                        printi("%s could not be found in the current directory of %s" % (csvFile, os.getcwd()))

                INDENT -= 1
                printi("1. Default Input")
                printi("2. CSV Input")
                printi("3. CSV File")
                printi("0. Go back")
                subChoice = input(prompt)
                INDENT += 1
            INDENT -= 1

        '''             '''
        ### GATHER MACS ###
        '''             '''
        if choice == "6":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            dashboard, found = getDashboard(apikey=apikey, maxRetry=10)
            prompt = "=(06)> "
            if bool(macDict):
                printi("MAC data already exists from a previous run")
                printi("1. Use current data")
                printi("2. Regenerate data")
                printi("0. Go back")
                subChoice = input(prompt)
                if subChoice == '0':
                    continue
                elif subChoice == '1':
                    printv("Using current data")
                elif subChoice == '2':
                    printi("Gathering MAC addresses from the network")
                    printi("Please wait as this can take a minute\n")
                    macDict = gatherMacs(dashboard=dashboard, devices=devices, networks=networks)
            else:
                printi("Gathering MAC addresses from the network")
                printi("Please wait as this can take a minute\n")
                macDict = gatherMacs(dashboard=dashboard, devices=devices, networks=networks)

            printi("1. Find by MAC and or Vendor")
            printi("2. List Vendors")
            printi("3. Show current data")
            printi("0. Go back")
            subChoice = input(prompt)
            INDENT += 1
            while subChoice != "0":
                if subChoice == '1':
                    printi("Enter CSV of MACs and or Vendors")
                    filter = input(prompt).strip()
                    vendors = [key for ven in filter.split(",")
                               for key in macDict.keys() if ven.lower() in key.lower()]
                    macs = [mac for mac in filter.split(",") if mac not in vendors and
                            re.match("^[0-9a-f]{2}([-:]?)[0-9a-f]{2}(\\1[0-9a-f]{2}){4}$", mac.lower())]
                    printv(vendors)
                    printv(macs)
                    findMacs(macDict=macDict, macs=macs, vendors=vendors)
                elif subChoice == '2':
                    data = [x for x in [[ven] for ven in macDict.keys()]]
                    data.insert(0, ['Vendors'])
                    printi("\n" + tabulate(data, headers='firstrow') + "\n")
                elif subChoice == '3':
                    printMacs(macDict)

                INDENT -= 1
                printi("1. Find by MAC and or Vendor")
                printi("2. List Vendors")
                printi("3. Show current data")
                printi("0. Go back")
                subChoice = input(prompt)
                INDENT += 1
                if subChoice == "0":
                    break
            INDENT -= 1

        '''                  '''
        ### GET SWTICH VLANS ###
        '''                  '''
        if choice == "7":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)

            prompt = "=(07)> "
            printi("1. Enter source switch Name, Serial, or IP")
            printi("2. List all currently selected switches")
            printi("3. Show current data")
            printi("4. Get switches with VLANs")
            printi("0. Go back")
            subChoice = input(prompt)
            INDENT += 1
            while subChoice != '0':
                if subChoice == "1":
                    printi("Enter name, serial, or IP")
                    filter = input(prompt)
                    sourceSwitch, found = is_device(devices, filter)
                    while not found:
                        printi("Could not find that device. Try again or 0 to go back")
                        filter = input(prompt)
                        if filter == "0":
                            break
                        sourceSwitch, found = is_device(devices, filter)
                    if filter == "0":
                        INDENT -= 1
                        break
                    temp = getSwitchVLANS(devices=[sourceSwitch])
                    switchVlans[sourceSwitch['name']] = temp[sourceSwitch['name']]
                    data = [[k, ','.join(str(x) for x in v)] for k, v in switchVlans.items()]
                    data.insert(0, ['Switch', 'VLANS'])
                    printi(tabulate(data, headers='firstrow'))
                elif subChoice == "2":
                    printi("Please wait as this information is gathered")
                    # We are overwriting here since we want all data to be reflective of the currently selected devices
                    switchVlans = getSwitchVLANS(devices=devices)
                    data = [[k, ','.join(str(x) for x in v)] for k, v in switchVlans.items()]
                    data.insert(0, ['Switch', 'VLANS'])
                    printi(tabulate(data, headers='firstrow'))
                elif subChoice == "3":
                    if bool(switchVlans):
                        data = [[k, ','.join(str(x) for x in v)] for k, v in switchVlans.items()]
                        data.insert(0, ['Switch', 'VLANS'])
                        printi(tabulate(data, headers='firstrow'))
                    else:
                        printi("No switch VLAN information has been gathered")
                elif subChoice == "4":
                    if bool(switchVlans):
                        printi("Enter CSV list of VLANs to look for")
                        INDENT += 1
                        subSubChoice = input(prompt)
                        vlans = []
                        for vlan in subSubChoice.split(","):
                            if is_int(vlan):
                                vlans.append(int(vlan))
                            else:
                                printi("\'%s\' is invalid" % vlan)
                                vlans = None
                                break
                        if vlans is not None:
                            # Only add a switch to our data list if one of the VLANs provided are on the switch
                            data = [[k, ','.join(str(x) for x in v)] for k, v in switchVlans.items()
                                    if any(x for x in vlans if x in v)]
                            data.insert(0, ['Switch', 'VLANS'])
                            printi(tabulate(data, headers='firstrow'))
                        INDENT -= 1

                INDENT -= 1
                printi("\n1. Enter source switch Name, Serial, or IP")
                printi("2. List all currently selected switches")
                printi("3. Show current data")
                printi("4. Get switches with VLANs")
                printi("0. Go back")
                subChoice = input(prompt)
                INDENT += 1
            INDENT -= 1

        '''                           '''
        ### PRINTING PORT INFORMATION ###
        '''                           '''
        if choice == "8":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)

            prompt = "=(08)> "
            printi("1. List single device")
            printi("2. List all currently selected switches")
            printi("3. Show current data")
            printi("4. Write current data to file")
            printi("0. Go back")
            subChoice = input(prompt)

            INDENT += 1
            while subChoice != "0":
                if subChoice == "1":
                    printi("Enter devce name, serial, or IP")
                    filter = input(prompt)
                    sourceSwitch, found = is_device(devices, filter)
                    while not found:
                        printi("Could not find that device. Try again or 0 to go back")
                        filter = input(prompt)
                        if filter == "0":
                            break
                        sourceSwitch, found = is_device(devices, filter)
                    if filter == "0":
                        break
                    temp = getSwitchPortCSV(dashboard=dashboard, devices=[sourceSwitch])
                    switchPorts[sourceSwitch['name']] = temp[sourceSwitch['name']]
                    printSwitchPorts(switchPorts)
                elif subChoice == "2":
                    switchPorts = getSwitchPortCSV(dashboard=dashboard, devices=devices)
                    printSwitchPorts(switchPorts)
                elif subChoice == "3":
                    if bool(switchPorts):
                        printSwitchPorts(switchPorts)
                    else:
                        printi("No data to show")
                elif subChoice == "4":
                    printi("Enter filename")
                    filename = input(prompt).strip()
                    f = open(filename, 'w')
                    data = []
                    for k in switchPorts.keys():
                        for ports in switchPorts[k]:
                            data.append([k] + [p for p in ports.values()])
                    data.insert(0, ['number', 'name', 'tags', 'enabled', 'poeEnabled', 'type', 'vlan',
                                    'voiceVlan', 'allowedVlans', 'rstpEnabled', 'stpGuard'])
                    f.write(tabulate(data, headers='firstrow'))
                    f.close()
                INDENT -= 1
                printi("1. List single device")
                printi("2. List all currently selected switches")
                printi("3. Show current data")
                printi("4. Write current data to file")
                printi("0. Go back")
                subChoice = input(prompt)
                INDENT += 1
            INDENT -= 1

        '''                    '''
        ### ACL/FIREWALL RULES ###
        '''                    '''
        if choice == "9":

            printi("Starting ACL Tool...")
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            prompt = "=(09)> "
            # Getting the network
            network = getNetwork(networks)
            networkId = None
            if network is not None:
                networkId = network['id']
            else:
                continue

            # Gathering the ACL and Firewall rules on that network
            printi("Fetching ACL-es")
            msACL, mxFirewall = getACLS(networkId)
            printi("Backing up ACL-es")
            msACL_bkp, mxFirewall_bkp = getACLS(networkId)
            printi("All information loaded")
            print("")

            # Memory hasn't been an issue since the 90s anyways
            aclChangeLog = [(msACL, mxFirewall)]
            currVersion = 1

            printi("1. Print MS ACL Rules")
            printi("2. Print MX Firewall Rules")
            printi("3. Trace Packet Through Rulesets")
            printi("4. Insert ACL Rule")
            printi("5. Delete ACL Rule")
            printi("6. Undo Last Action")
            printi("7. Compare to Previous Versions")
            printi("8. Commit ACL Changes")
            printi("0. Exit")

            INDENT += 1
            subChoice = input(prompt)

            while subChoice != "0":

                if subChoice == '1':
                    printACLS(msACL)
                elif subChoice == '2':
                    if mxFirewall is None:
                        printi("No MX on this network")
                    else:
                        printACLS(mxFirewall)
                elif subChoice == '3':
                    INDENT += 1
                    printi("Provide Source or 0 to go back")
                    printi("Ex. any or 192.168.1.1 or 10.160.34.0/24")
                    src = getAddress()
                    if src == '0':
                        continue
                    printi("Provide Destination or 0 to go back")
                    printi("Ex. any or 192.168.1.1 or 10.160.34.0/24")
                    dst = getAddress()
                    if dst == '0':
                        continue
                    if mxFirewall is not None:
                        tracePacketInACL(src, dst, msACL + mxFirewall)
                    else:
                        tracePacketInACL(src, dst, msACL)
                    INDENT -= 1
                elif subChoice == '4':
                    INDENT += 1
                    printi("Provide position or 0 to go back")
                    printi("Ex. MS-01 or MX-15")
                    printv(len(msACL))
                    position = input(prompt).strip().upper()
                    while position != "0":
                        valid = False
                        inputCheck = re.search('M(S|X)-\d\d', position)
                        device = None
                        number = None
                        if inputCheck is None:
                            printi("Invalid input.")
                        else:
                            device = position.split("-")[0]
                            spot = int(position.split("-")[1])

                            # MS Validation
                            if device == 'MS':
                                msLen = len(msACL)
                                if msLen == 0 and (spot == 0 or spot == 1):
                                    printv("ACL rule will be placed at the beginning of the list")
                                    valid = True
                                elif msLen != 0 and (0 <= spot <= msLen):
                                    printv("ACL rule will be place in the valid position of %d" % spot)
                                    valid = True
                                else:
                                    printi("%s is not valid MS ACL placement" % position)
                            # MX Validation
                            if mxFirewall is not None and device == 'MX':
                                mxLen = len(mxFirewall)
                                if mxLen == 0 and (spot == 0 or spot == 1):
                                    printv("Firewall rule will be placed at the beginning of the list")
                                    valid = True
                                elif msLen != 0 and (0 <= spot <= msLen):
                                    printv("Firewall rule will be place in the valid position of %d" % spot)
                                    valid = True
                                else:
                                    printi("%s is not a valid MX Firewall placement" % position)
                        if valid:
                            if "MS" in position.split("-")[0]:
                                aclChangeLog.append((msACL, mxFirewall))
                                msACL = insertACL(position, msACL)
                                currVersion += 1
                            elif mxFirewall is not None and "MX" in position.split("-")[0]:
                                aclChangeLog.append((msACL, mxFirewall))
                                mxFirewall = insertACL(position, mxFirewall)
                                currVersion += 1
                        INDENT -= 1
                        printi("Provide position or 0 to go back")
                        printi("Ex. MS-01 or MX-15")
                        printv(len(msACL))
                        position = input(prompt).strip().upper()
                        INDENT += 1
                    INDENT -= 1
                elif subChoice == '5':
                    INDENT += 1
                    printi("Provide either a range or single ACL to delete or 0 to go back")
                    printi("ex. MS-10-MX-02 or MS-03 or MX-07")
                    deleting = input(prompt).upper()
                    if deleting == '0':
                        continue
                    else:
                        aclChangeLog.append((msACL, mxFirewall))
                        msACLTemp, mxACLTemp = deleteACL(deleting, msACL, mxFirewall)
                        if msACLTemp is None and mxACLTemp is None:
                            printv("The delete ACL call failed")
                        else:
                            currVersion += 1
                            if msACLTemp is not None:
                                printv("Changing MS ACL list")
                                msACL = msACLTemp
                            if mxACLTemp is not None:
                                printv("Changing MX ACL list")
                                mxFirewall = mxACLTemp
                            aclChangeLog.append((msACL, mxFirewall))
                    INDENT -= 1
                elif subChoice == '6':
                    INDENT += 1
                    if currVersion == 1:
                        printi("No previous version to revert to")
                    else:
                        printv("Going from version %d to %d" % (currVersion, currVersion - 1))
                        printi("Reverting ACL-es to last made change")
                        aclChangeLog.append((msACL, mxFirewall))
                        currVersion += 1
                        msACL, mxFirewall = aclChangeLog[currVersion - 2]
                    INDENT -= 1
                elif subChoice == '7':
                    if currVersion == 1:
                        printi("No changes have been yet")
                    else:
                        printi("Select version to compare to or 0 to go back")
                        printi("Available versions: %s" % ",".join([str(i) for i in range(1, currVersion)]))
                        INDENT += 1
                        version = input(prompt)
                        while not is_int(version):
                            printi("Invalid Entry")
                            printi("Select version to compare to or 0 to go back")
                            printi("Available versions: %s" % ",".join([str(i) for i in range(1, currVersion)]))
                            version = input(prompt)
                        if version == '0':
                            INDENT -= 1
                            continue
                        else:
                            version = int(version)
                        printv("Comparing version %d to %d" % (currVersion, version))
                        msTemp, mxTemp = aclChangeLog[version]
                        printi("Comparing MS ACL-es")
                        compareACLs(msACL, msTemp)
                        if mxFirewall is not None:
                            printi("Comparing MX ACL-es")
                            compareACLs(mxFirewall, mxTemp)
                        INDENT -= 1
                elif subChoice == '8':
                    if (msACL is not None and msACL == aclChangeLog[0][0]) or \
                            (mxFirewall is not None and mxFirewall == aclChangeLog[0][1]):
                        printi("No changes to be committed")
                    else:
                        INDENT += 1
                        printi("Hit enter to continue or 0 to go back")
                        subchoice = input(prompt)
                        if subchoice == '0':
                            continue
                        else:
                            result = commitACLs(dashboard, networkId, msACL, mxFirewall)
                            if result == -1:
                                INDENT -= 1
                                continue
                            if result == 0:
                                INDENT -= 1
                                break

                INDENT -= 1
                printi("1. Print MS ACL Rules")
                printi("2. Print MX Firewall Rules")
                printi("3. Trace Packet Through Rulesets")
                printi("4. Insert ACL Rule")
                printi("5. Delete ACL Rule")
                printi("6. Undo Last Action")
                printi("7. Compare to Previous Versions")
                printi("8. Commit ACL Changes")
                printi("0. Exit")
                INDENT += 1
                subChoice = input(prompt)
            INDENT -= 1

        '''                         '''
        ### Link Aggregation Groups ###
        '''                         '''
        if choice == "10":
            # This will eventually be expand out to include deletion and adding but for now it is just printing
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)
            prompt = "=(10)> "
            if aggDict is None:
                # Getting the network
                network = getNetwork(networks)
                networkId = None
                if network is not None:
                    networkId = network['id']
                else:
                    continue
                printi("Gathering Link Aggregation Groups")
                aggs = getAggs(dashboard, devices, networkId)
                if aggs is not None:
                    aggDict = dict()
                    aggDict['original'] = aggs[0]
                    aggDict['formatted'] = aggs[1]
                    INDENT += 1
                    printAggs(aggDict['formatted'])
                    INDENT -= 1
                else:
                    printi("There were no aggregation groups found")
            else:
                printi("LAGG data already present.")
                printi("1. Regather information")
                printi("2. Print current informtaion")
                printi("0. Go Back")
                INDENT += 1
                subChoice = input(prompt)
                if subChoice == "1":
                    # Getting the network
                    network = getNetwork(networks)
                    networkId = None
                    if network is not None:
                        networkId = network['id']
                    else:
                        printv("Invalid network")
                        continue
                    aggs = getAggs(dashboard, devices, networkId)
                    aggDict['original'] = aggs[0]
                    aggDict['formatted'] = aggs[1]
                    printAggs(aggDict['formatted'])
                elif subChoice == "2":
                    printAggs(aggDict['formatted'])
                elif subChoice == "0":
                    printv("Going back")
                INDENT -= 1

        '''                   '''
        ### SETTING VARIABLES ###
        '''                   '''
        if choice == "11":
            networks, devices = checkVariables(networks=networks, devices=devices,
                                               networkFilter=networkFilter, deviceFilter=deviceFilter)

            prompt = "=(11)> "
            printi("1. Manage Network Filters")
            printi("2. Manage Switch Filters")
            printi("3. Toggle Verbosity")
            printi("0. Go Back")
            subChoice = input(prompt)

            while True:

                # BREAK OUT
                if subChoice == "0":
                    break

                # NETWORK FILTER
                if subChoice == "1":

                    INDENT += 1
                    if networkFilter:
                        printi("Current Filters:")
                        for filter in networkFilter:
                            printi("> %s" % ','.join(filter))
                        print()
                    else:
                        printi("No filters currently set")

                    # Updating our device list
                    printi("Selected Networks")
                    for network in networks:
                        printi(network['name'])

                    printi("1. Filter out current network list")
                    printi("2. Remove network from list")
                    printi("3. Add network to list")
                    printi("4. Clear current filters and start fresh")
                    printi("0. Go back")
                    subSubChoice = input(prompt).strip()

                    while subSubChoice != '0':

                        INDENT += 1

                        if subSubChoice == '1':
                            printi("Enter in new comma separated filter or 0 to go back")
                            newfilter = input(prompt).strip()
                            if newfilter == '':
                                while newfilter != '0':
                                    printi("Enter in new comma separated filter or 0 to go back")
                                    newfilter = input(prompt).strip()
                            if newfilter == '0':
                                continue
                            newfilter = newfilter.replace("\"", '').split(",")
                            networkFilter.append(newfilter)
                            printi("New Filter: %s" % ','.join(newfilter))

                            networks = getNetworks(dashboard=dashboard, filterOut=networkFilter)

                        elif subSubChoice == '2':
                            for network in networks:
                                printi(network['name'])
                            printi("Enter in name of network to remove or 0 to go back")
                            subSubSubChoice = input(prompt).strip()
                            while subSubSubChoice != '0':
                                found = False
                                for network in networks:
                                    if 'name' in network and subSubSubChoice.lower() in network['name'].lower():
                                        printv("Network found %s " % network['name'])
                                        found = True
                                        networks.remove(network)
                                        printi("%s has been removed" % network['name'])
                                        break
                                if not found:
                                    printi("Network not found")
                                printi("Enter in name of device to add or 0 to go back")
                                subSubSubChoice = input(prompt).strip()

                        elif subSubChoice == '3':
                            for network in networks:
                                printi(network['name'])
                            printi("Enter in name of network to add or 0 to go back")
                            subSubSubChoice = input(prompt).strip()
                            while subSubSubChoice != '0':
                                found = False
                                for network in getNetworks(dashboard=dashboard, filterOut=None):
                                    if 'name' in network and subSubSubChoice.lower() in network['name'].lower():
                                        printv("Network found %s " % network['name'])
                                        found = True
                                        networks.append(network)
                                        printi("%s has been added" % network['name'])
                                        break
                                if not found:
                                    printi("Network not found")
                                printi("Enter in name of device to add or 0 to go back")
                                subSubSubChoice = input(prompt).strip()

                        else:
                            printv("Clearing filters")
                            printi("Current Filters:")
                            for filter in networkFilter:
                                printi("> %s" % ','.join(filter))
                            print()
                            networkFilter = []
                            printi("Enter in new comma separated filter or enter for none")
                            newFilter = input(prompt).strip()
                            if newFilter == '':
                                newFilter = None
                            else:
                                newFilter = newFilter.replace("\"", '').split(",")
                                networkFilter.append(newFilter)
                                printi("New Filter: %s" % ','.join(newFilter))
                            devices = getNetworks(dashboard=dashboard, filterOut=networkFilter)

                        printi("Selected Networks")
                        for network in networks:
                            printi(network['name'])

                        INDENT -= 1
                        printi("1. Filter out current network list")
                        printi("2. Remove network from list")
                        printi("3. Add network to list")
                        printi("4. Clear current filters and start fresh")
                        printi("0. Go back")
                        subSubChoice = input(prompt).strip()

                    INDENT -= 1
                    # Updating our device list
                    printi("Refreshing device list with new network list")
                    devices = getDevices(dashboard=dashboard, networks=networks, deviceFilter=deviceFilter)

                # DEVICE FILTER
                elif subChoice == "2":
                    if deviceFilter:
                        INDENT += 1
                        printi("Current Filters:")
                        for filter in deviceFilter:
                            printi("> %s" % ','.join(filter))
                        INDENT -= 1
                        print()
                    else:
                        printi("No filters currently set")

                    INDENT += 1
                    printi("1. Filter out current device list")
                    printi("2. Filter in current device list")
                    printi("3. Remove device from list")
                    printi("4. Add device to list")
                    printi("5. Clear current filters and start fresh")
                    printi("0. Go back")
                    subSubChoice = input(prompt).strip()

                    while subSubChoice != '0':

                        INDENT += 1

                        if subSubChoice == '1' or subSubChoice == '2':
                            printi("Currently selected devices")
                            printDevices(devices=devices, columns=5)
                            printi("Enter in new comma separated filter")
                            newfilter = input(prompt).strip()
                            newfilter = newfilter.replace("\"", '').split(",")
                            deviceFilter.append(newfilter)
                            printi("New Filter: %s" % ','.join(newfilter))
                            if subSubChoice == '1':
                                devices = getDevices(dashboard=dashboard,
                                                     networks=networks,
                                                     deviceFilter=deviceFilter,
                                                     devices=devices
                                                     )
                            else:
                                devices = getDevices(dashboard=dashboard,
                                                     networks=networks,
                                                     deviceFilter=deviceFilter,
                                                     devices=devices,
                                                     filterIn=True,
                                                     filterOut=False
                                                     )

                        elif subSubChoice == '3':
                            printi("Currently select devices")
                            printDevices(devices, 5)
                            printi("Enter in name of device to remove or 0 to go back")
                            subSubSubChoice = input(prompt).strip()
                            while subSubSubChoice != '0':
                                found = False
                                for device in devices:
                                    if 'name' in device and subSubSubChoice.lower() in device['name'].lower():
                                        printi("Device found: %s" % device['name'])
                                        devices.remove(device)
                                        printi("Device removed")
                                        found = True
                                        break
                                if not found:
                                    printi("Device not found")
                                printi("Enter in name of device to remove or 0 to go back")
                                subSubSubChoice = input(prompt).strip()
                                if subSubSubChoice == '0':
                                    break

                        elif subSubChoice == '4':
                            printi("Gathering original list of devices")
                            ogDevices = getDevices(dashboard, networks, deviceFilter=None)
                            printDevices(devices, 5)
                            printi("Enter in name of device to add or 0 to go back")
                            subSubSubChoice = input(prompt).strip()
                            while subSubSubChoice != '0':
                                found = False
                                for device in ogDevices:
                                    if 'name' in device and subSubSubChoice.lower() in device['name'].lower():
                                        printv("Device found %s " % device['name'])
                                        if device in devices:
                                            printi("%s already in device list" % device['name'])
                                            found = True
                                            break
                                        else:
                                            devices.append(device)
                                            printi("Device added")
                                            found = True
                                            break
                                if not found:
                                    printi("Device not found")
                                printi("Enter in name of device to add or 0 to go back")
                                subSubSubChoice = input(prompt).strip()

                        else:
                            printv("Clearing filters")
                            printi("Current Filters:")
                            for filter in deviceFilter:
                                printi("> %s" % ','.join(filter))
                            print()
                            deviceFilter = []
                            printi("Enter in new comma separated filter or enter for none")
                            newFilter = input(prompt).strip()
                            if newFilter == '':
                                newFilter = None
                            else:
                                newFilter = newFilter.replace("\"", '').split(",")
                                deviceFilter.append(newFilter)
                                printi("New Filter: %s" % ','.join(newFilter))
                            devices = getDevices(dashboard=dashboard,
                                                 networks=networks,
                                                 deviceFilter=deviceFilter,
                                                 devices=None
                                                 )
                        printi("Newly selected devices")
                        # Since this is still an array of dicts we have to use lambda to sort them by their name key
                        devices.sort(key=lambda x: x['name'])
                        # Using an auxiliary function to print the devices out into columns
                        printDevices(devices=devices, columns=5)

                        INDENT -= 1
                        printi("1. Filter out current device list")
                        printi("2. Filter in current device list")
                        printi("3. Remove device from list")
                        printi("4. Add device to list")
                        printi("5. Clear current filters and start fresh")
                        printi("0. Go back")
                        subSubChoice = input(prompt).strip()

                    INDENT -= 1

                # VERBOSITY TOGGLE
                elif subChoice == "3":
                    if VERBOSE:
                        VERBOSE = False
                        printi("Verbosity turned off")
                    else:
                        VERBOSE = True
                        printi("Verbosity turned on")

                # MENU
                printi("1. Manage Network Filters")
                printi("2. Manage Switch Filters")
                printi("3. Toggle Verbosity")
                printi("0. Go Back")
                subChoice = input(prompt)
            INDENT -= 1

        '''             '''
        ### Manage Data ###
        '''             '''
        if choice == "12":
            # Since the purpose of this function is to print out the major variables, we can assume that if the devices
            # and or networks variable has not been set, then the others are not either
            prompt = "=(12)> "
            if networks is None or devices is None:
                printi("No session has been started")
            else:
                printi("1. Save gathered data")
                # printi("2. Load previous session data") I will add this soon
                printi("0. Go Back")
                INDENT += 1
                subChoice = input(prompt)
                if subChoice == "0":
                    INDENT -= 1
                    continue
                else:
                    currTime = str(int(time.time()))
                    with open(currTime + "_networks.json", 'w') as f:
                        printi("Saving Networks data to " + currTime + "_networks.json")
                        json.dump(networks, f)
                        f.close()
                    with open(currTime + "_devices.json", 'w') as f:
                        printi("Saving Device data to " + currTime + "_devices.json")
                        json.dump(devices, f)
                        f.close()
                    with open(currTime + "_macs.json", 'w') as f:
                        printi("Saving MAC data to " + currTime + "_macs.json")
                        json.dump(macDict, f)
                        f.close()
                    with open(currTime + "_vlans.json", 'w') as f:
                        printi("Saving VLAN data to " + currTime + "_vlan.json")
                        json.dump(switchVlans, f)
                        f.close()
                    with open(currTime + "_ports.json", 'w') as f:
                        printi("Saving Port data to " + currTime + "_ports.json")
                        json.dump(switchPorts, f)
                        f.close()
                    if aggDict is not None:
                        with open(currTime + "_lagg.json", 'w') as f:
                            printi("Saving LAGG data to " + currTime + "_lagg.json")
                            json.dump(aggDict, f)
                            f.close()
                    INDENT -= 1



