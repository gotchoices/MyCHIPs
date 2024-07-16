# MyCHIPs Mobile

## Directory Structure
This folder contains/supports multiple implementations of a MyCHIPs mobile application:

- . (client):  
  Support files common to any implementation.

- flutter:  
  The original BYU Capstone dart/flutter-based app.
  Implemented certain aspects of a UI but never had a working API connection
  to the backend.  To continue flutter development, it will be necessary
  to replicate the two wyseman modules: client_ws, client_msg (and eventually
  client_np).

- chark: CHip App React Kyle  
  Originally, an effort at a React Native app to demonstrate usage of the 
  Wyseman JS client API.  Insight Workshop worked from this version to create
  a fully working app, now (May 2024) available on IOS and Android.

## React Native Setup Notes for Mac OS Host
Install node from node.js.org (pre-built installer or n, nvm, etc).
Install/update xcode to latest version.

Install file watcher to monitor file changes and auto load the app:
```
brew install watchman
```

Install a Java JDK.  This one is recommended by React Native:
```
  brew tap homebrew/cask-versions
  brew install --cask zulu11
```

Install Android Studio and Applicable SDK(s).
Follow **carefully and precisely** the process in the
[instructions](https://reactnative.dev/docs/environment-setup).
Note, there are separate setup details for building android and ios.

React Native previously recommended a specific version of ruby (2.7.5).
Instructions currently (May 2024) say you can use the version of ruby
that ships with the "latest version of macOS."

If you need a specific version, you can do that via rvm [instructions](https://rvm.io/rvm/install):
```
  curl -sSL https://get.rvm.io | bash -s stable
  source ~/.rvm/scripts/rvm
  rvm install 2.7.5
  rvm use 2.7.5
```

You should be able to install cocoapods with one of the following:
```
  sudo gem install cocoapods		#system-wide
  gem install cocoapods			#local user
```

## Running the Emulator
Now get into the client root directory:
```
cd mychips/clients
```
Android:  
Make sure you have one or more android emulators (Virtual Devices) configured in android studio.

If you are connecting to a local MyCHIPs server that doesn't have a public 
domain name, IP address and SSL certificate, you need to take several steps:
- Run a local DNS service that can resolve the hostname of the
  MyCHIPs server (see notes below).
- Run the emulator so it can access that DNS server
- Install the CA certificate with which the server's certificate was signed.

There is a script provided:
```
./runemu
```
This script will check to make sure there is a DNS server running at the
specified address.  This is by default 127.0.0.1 from the perspective of
the host (itself).  From the perspective of the emulator, it is 10.0.2.2
which also resolves to the host.  It then launches the emulator with
the internal DNS pointed to the host.

The script will also copy the CA certificate from the server's pki/local
directory to the running emulator's Download folder.  This should be 
valid for any host certificates built in the same directory.  It will 
then launch the settings menu on the emulator.  You will have to manually 
search for "certificates" in settings, navigate to the download folder
and click the certificate file to install it on the emulator.  You should
only have to do this once (unless/until you wipe the emulator data).

There is not currently a scripted method for configuring the ios simulator.
However, the ios simulators seem to read the host's /etc/host file fine.
To get it to accept a locally signed certificate, you might try opening
Safari on the emulator and browing:
```
  https://your-server:8443
```
and confirming the warnings that you really want to visit the insecure site.

There is also an xcode command for installing a root certificate on a
simulator.  Something like:
```
  xcrun simctl keychain booted add-root-cert ../../pki/local/web-ca.crt
```

Start react native and the metro bundler in a shell window:
```
cd chark
npm start
```
Client debug messages will also render in that shell window.

In a separate shell, run the app:
```
cd chark
npm run android		#For android

npm run ios		#For ios
```
The app should compile and load into the emulator.

## Local DNS Server
If you are running the server in a local VM or docker container, it
may be helpful to run a local DNS server, as noted above, so the emulator 
can find the correct IP number for the backend.

You might use dnsmasq for this purpose as follows:
```
  brew install dnsmasq
  /usr/local/sbin/dnsmasq
```
This will resolve any hostnames you have in your local /etc/hosts file.
It should pass any other requests onto whatever nameserver your host
is using.  So if you are running the server on a virtual linux machine
called linux0, it might have a local IP address (on the host) of 
192.168.56.10, for example.
With dnsmasq running, you should be able to resolve to that IP with:
```
  dig @localhost linux0
```
It may not work as you intend to resolve the server hostname to
127.0.0.1 since the route will originate inside the emulator itself.
Use the actual address of the host or some address that will
resolve correctly to the VM/container.

## Connecting to the Server
Make sure the MyCHIPs backend is running with something like:
```
export NODE_DEBUG=debug
cd mychips
npm start			#native Linux, or
npm run docker-dev		#in docker
```
Debugging info will be available from the backend using something like this:
```
tail -f /var/tmp/mychips/combined.log			#or
tail -f test/local/docker/mychips0.log/combined.log
```
If you haven't already, it will be helpful to initialize the backend database 
with some data:
```
cd mychips/test/sample
./kickstart			#native
./randuser -n 4

or
docker exec mychips0 test/sample/kickstart
docker exec mychips0 test/sample/randuser -n 4
```

Now generate a one-time connection token URL and use it to connect to
the server with something like:
```
bin/adminticket -i p1000 -q |./linklaunch			#or
docker exec mychips0 bin/adminticket -i p1000 -q |./linklaunch	#or
ssh user@server /path/to/mychips/bin/adminticket -i p1000 -q |./linklaunch

The linklaunch script will first attempt to connect to a running android
emulator.  If none is found, it will try to connect to a running IOS emulator.

### Hard-coded Connection Token (deprecated)
If deep linking is not working, you may try:

```
mychips/bin/adminticket >chark/assets/ticket.json -i p1000	#or
docker exec mychips0 bin/adminticket -i p1000 >chark/assets/ticket.json
```
Note: this example creates a ticket for user p1000 and hard-copies
it into the filesystem of the app.

Press the connection indicator in the app to bring up a debug
connection dialog.  Press "Connect with Token."

See that the connection indicator turns green.  This indicates that you 
successfully connected.  If it is not green, the problem likely lies
with one of these two issues:
- The emulator can't reach the server
- The emulator doesn't like the server's certificate

### Other Notes / Caveats

#### Metro Launch
During the ios build, react-native uses curl to query http://localhost:8081/status
to determine if the metro bundler is running.  If you have http_proxy defined
on your system, make sure you also have no_proxy set with your local domain
information to exclude localhost from proxy traffic.
Otherwise, the build will not find your running metro and will attempt to 
launch a new one (which will fail because the port will already be in use).

#### Metro Symlinks
The Metro bundler doesn't seem to support symlinks.  This creates
a problem running wyseman out of a local source folder
(as opposed to what may be fetched from npmjs.org).

There is a work-around included.  Execute:
```
npm develop
```
This will delete whatever wyseman is in chark/node_modules.
It will then make a fresh copy from a local source copy of the wyseman library
if it can be found parallel to the mychips project.
Finally, it will set up a watchman process on wyseman so if you make
any changes to the libraries chark is using, it will copy them into node_modules.

#### Realpath
When first running the android build, the following error came up:
"Command failed: couldn't find realpath command".
This was fixed by installing realpath using:
```
brew install coreutils
```

#### RN 0.68 to 0.69
Had problem running on IOS, Fix here:
  https://stackoverflow.com/questions/72729591/fbreactnativespec-h-error-after-upgrading-from-0-68-x-to-0-69-0

