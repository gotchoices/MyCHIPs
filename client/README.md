# MyCHIPs Mobile

## Directory Structure
This folder contains several different attempts/implementations of a MyCHIPs
mobile application:

- . (client):  
  Support routines common to any implementation.

- flutter:  
  The original BYU Capstone dart/flutter-based app.
  Implemented certain aspects of a UI but never had a working API connection
  to the backend.  To continue flutter development, it will be necessary
  to replicate the two wyseman modules: client_ws, client_msg (and eventually
  client_np).

- chark: CHip App React Kyle
	An effort at a React Native app to demonstrate usage of the Wyseman
	JS client API.  Hopefully will become the first standard MyCHIPs app.

## Setup Notes
These notes reflect steps taken on MacOS to get the React Native app running
for Android:  Also see: https://reactnative.dev/docs/environment-setup

File watcher to monitor file changes and auto load the app:
```
brew install watchman
```

Need a working Java JDK.  This one is recommended by React Native:
```
  brew tap homebrew/cask-versions
  brew install --cask zulu11
```

Need to install Android Studio and SDK 12.
Follow carefully and precisely the process in the web link above
(there are separate setup details for building android and ios).

The instructions require a specific version of ruby (2.7.5 or 2.7.6?).
Here are some approaches to consider.

Via brew:
```
  brew install cocoapods
  brew install ruby@2.7
  brew link ruby@2.7
```
Via rvm (https://rvm.io/rvm/install):
```
  gpg --keyserver hkp://pgp.mit.edu --recv-keys 409B6B1796C275462A1703113804BB82D39DC0E3 7D2BAF1CF37B13E2069D6956105BD0E739499BDB
  curl -sSL https://get.rvm.io | bash
  source ~/.rvm/scripts/rvm
  rvm install 2.7.5
  rvm use 2.7.5
  gem install cocoapods
```

Next, get into the area for mobile apps:
```
cd mychips/clients
```

Make sure you have one or more android emulators (Virtual Devices) configured.
Then launch an instance of an emulator using the provided script:
```
./runemu
```
This script will also configure the emulator as follows:
- Install a host file that will direct web traffic destined for address
  mychips0 to the local host computer where hopefully you have the mychips
  backend running.  If it is running somewhere else, you will have to
  modify the client/host file so the emulator can find the correct address.
- Install a custom CA file.  This will be copied from the pki/local
  folder.  If you are using some other certificate system, you will need
  to adapt the script for your own needs.

Start react native and the metro bundler in a shell window:
```
cd chark
npx react-native start
```
Client debug messages will also render in that shell window.

In a separate shell, run the app for android:
```
cd chark
npx react-native run-android
```
The app should now be running on the emulator.

Make sure the MyCHIPs backend is running.  Something like:
```
export NODE_DEBUG=debug
cd mychips
npm run docker-dev		#docker, or
npm start			#native
```
Debugging info will be available from the backend using something like this:
```
tail -f test/local/docker/mychips0.log/combined.log	#or
tail -f /var/tmp/mychips/combined.log
```
If you haven't already, it will be helpful to initialize the backend database 
with some data:
```
docker exec mychips0 test/sample/kickstart
docker exec mychips0 test/sample/randuser -n 4

or
cd mychips/test/sample
./kickstart
./randuser -n 4
```
Now generate a one-time connection token from the backend:

NOTE: This method is deprecated.  See more current deep link method below.
```
docker exec mychips0 bin/adminticket >chark/assets/ticket.json	#or
mychips/bin/adminticket >chark/assets/ticket.json
```
Note: this example creates a ticket for the admin user and hard-copies
it into the filesystem of the app.  This is only applicable in the very
early stages of chark where the ticket is hard-loaded by the require
command.  Later development should use a QR code or a deep link.

Press the app button: "Connect with Token."

See that the Server: line at the top of the app is updated to show the
server portal: mychips0:54320.  This indicates that you successfully
connected.  You can also see in the backend debugging window a "true"
status in the validation line.

Press the app button: "Query Backend."

See that some user data is displayed in the client debugging window.
This indicates that data was successfully fetched from the backend.

Press the app button: "Disconnect."

The backend debugging should indicate that you have disconnected.
The app "Server:" line should go blank.

Press the app button: "Connect with Key."

You should get successfully reconnected and be able to query data again.
You should be able to disconnect/reconnect any number of times using
the key.

### Deep Links
Mobile apps should support launching with a deep link prefixed with 'mychips' for example:
```
adb shell am start -W -a android.intent.action.VIEW -d 'mychips://connect?host=mychips0\&port=54320\&token=b4179431fd18d5abbde31f3e391a3d99\&user=p1000'
```
Note, by the time the link has been passed through bash and then the adb shell
the amersand's will cause a problem if they are not escaped.
So one method is to first produce the connection ticket deep link using:
```
mychips/bin/adminticket -i <user_id> -q
```
next, copy/paste it onto the command line with the above adb command and
then insert a backslash before each ampersand before executing.

This can be a little awkward especially since the backend may be running
on a different machine, VM, docker instance, etc.
There is a script in this folder to help with this so you can do something like:
```
docker exec mychips0 bin/adminticket -i p1000 -q |./linklaunch	#or
bin/adminticket -i p1010 -q |./linklaunch


### Other Notes / Caveats
The Metro bundler doesn't seem to support symlinks.  This creates
a problem running wyseman out of the local source folder.

To do so, follow these instructions:
https://medium.com/@alielmajdaoui/linking-local-packages-in-react-native-the-right-way-2ac6587dcfa2

When I ran the run-android command, I got an error:
"Command failed: couldn't find realpath command".
I had to install realpath using:
```
brew install coreutils
```

Can check the status of running emulator(s) using:
```
adb devices		#or:
~/Library/Android/sdk/platform-tools/adb devices

```

Setting up React Navigation: https://reactnavigation.org/docs/getting-started
(Follow procedures for both Android and IOS)
```
  npm install --save @react-navigation/native
  npm install --save react-native-screens react-native-safe-area-context
  npx pod-install ios
  npm install --save @react-navigation/native-stack
```

Had problem running on IOS, Fix here:
  https://stackoverflow.com/questions/72729591/fbreactnativespec-h-error-after-upgrading-from-0-68-x-to-0-69-0

