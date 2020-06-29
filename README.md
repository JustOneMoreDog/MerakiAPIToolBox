# MerakiAPIToolBox
The closest one can get to a CLI on Meraki

### Features
* Find switches by serial, IP, or name
* Get network wide switch port usage stats
* Get LLDP information across devices 
* Copy switch port configurations in either a one off or CSV style
* Locate where a vendor and or MAC address exists on the network
* Show which VLANs are being used on which switches
* Gather port configurations across any number of devices
* Backup port configurations across any number of devices into a CSV file
* Manage MS ACL and MX Firewall rules in a testing environmnet
  * Show existing rules
  * Trace source and destination IP-es and or networks through current rulesets
  * Insert new rule into working set
  * Delete rules
  * Compare changes made during session
  * Commit changes to production
* Display Link Aggregation Groups
* Filter out or in networks to work with
* Filter out or in devices in devices within selected networks to work with
* Save gathered information to file

### Prerequisites
Use pip to ensure you have all the required modules
```
pip3 install -r requirements.txt
```

### Contributing
You are more than welcome to fork this repository, make your changes and submit a pull request — https://github.com/picnicsecurity/MerakiAPIToolBox/pulls

### Planned Feature Additions
* Changing the WiFi password and emailing the required people
* Load session from previously saved session save
* Better error catching
* Creation and deletion of link aggregation groups
* Getting, adding, deleting layer 3 interfaces on MS switches (pending API feature addition)
* Read only mode

### Warrenty
As always, you should understand the code you are running and in what environment you are running it in. These scripts are provided "as is". See the license file for more information.   

### Why?
I found myself working with Meraki at my job and found the API to be more responsive and handle bulk changes better than the Dashboard. I also wanted to learn Python as I had not worked with it prior to this. Thus this seemed like the perfect oppurtunity to both learn Python and make my job easier. This started out with just being able to find switches on my network but kept growing until it reached where it is today.
