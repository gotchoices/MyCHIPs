<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="use-native.md">Next</a>
</div>

### Docker Test Instance

This is a quick and simple way to launch MyCHIPs for simple testing and evaluation.
This is easier on Mac (and perhaps Windows) than on Linux because docker under Linux 
has certain additional [permission issues](https://docs.docker.com/engine/install/linux-postinstall/).

You will need node/npm installed and docker running on your host system.

To launch a single server/database pair in development mode:
```
  npm run docker
```
This will probably take a while on first run as it has to build images.
It should be faster on subsequent runs.
Once containers are launched, it will run until you interrupt it with a CTRL-C.
You can also use this command to stop and remove the containers:
```
  npm run docker-stop
```
The server is configured from the file build/config.sh for either a production or development run-time profile.
The hostname specified there for the MyCHIPs server (mychips0) will have to resolve to your system.
For testing, you can solve this with a line in /etc/hosts (or C:\Windows\System32\drivers\etc\hosts) as follows:
```
  127.0.0.1	mychips0
```
We will use this hostname in the browser URL bar to run the admin web app.
This is also what will get built into the SSL certificates so everything has to 
use the same hostname for the browser to be happy over https.

Once the server pair is running, we would like to connect to it using the admin UI.
But the backend will not allow this without an authorized connection token.
You can create one using the following bootstrap command:
```
  docker exec mychips0 bin/adminticket -Q	#or:
  docker exec mychips0 bin/adminticket -S webPort -P WSPort -H mychips0 -Q
```
The https SPA (Single Page Application) port and WebSocket ports in the second example
must match up with what is in the config-dev.env file for the server pair you just launched.
The bootstrap command will output a URL (containing the connection token) which 
you can copy/paste into your browser.  Or if you are really tricky you can do 
it all in one step with something like this (on Mac OS):
```
  open -n -a Firefox.app --args -new-tab \
    $(docker exec mychips0 bin/adminticket -H mychips0 -Q)
```
Next, the browser will complain that you are connecting to an SSL web server 
using a certificate signed by an unknown certificate authority.
To fix that, you can import the CA file created by the software as follows (again for Mac OS):
```
  open test/local/docker/pki/web-ca.crt
```
You will need to tell the OS (in Keychain Access) to fully trust this CA.
The certificate is called: Chippies.chip.

Windows has a similar system for importing certificate authorities.
For Linux, you may have to import it directly into the browser you are using.
Firefox users may also have to restart the browser after installing a certificate.

Now generate a fresh connection ticket as noted above and try again.
(Connection tickets only last for a few minutes and they can only be used/tried once.)

The MyCHIPs server should be creating logs which you can view with:
```
  tail -f test/local/docker/mychips0.log/combined.log
```
If you can't find these logs, check:
- Is the mychips0.log folder created with permissions that allow the container to log to it?
- Is the mychips0.log folder getting properly mounted under the container (at /var/tmp/mychips)?
- Is the mychips main folder getting properly mounted under the container (at /usr/local/devel)?

The PostgreSQL server creates logs you can view with this command:
```
  docker logs -f postgres0 --tail -0
```
Once connected, you should be able to view users by finding the "Load All" button
in the smaller hamburger menu on the upper left area of the preview window.  
There will probably be only a single user: admin.

To make things more interesting, try this:
```
  docker exec mychips0 test/sample/randuser -n 4
```
Now reload the preview to see 4 more users on your system.  Double click on 
one of those users to open an editing pane.  Execute the Actions menu item 
in the editing pane to generate a connection ticket for that user.  This
displays a QR code by default, but there are also links there to copy/paste a 
URL into a browser to connect to the User (as opposed to admin) UI.

### Docker Development Mode
There is also a build profile for running a development docker instance that can be launched as follows:
```
  npm run docker-dev
```
This is more useful if you want to modify the server code.

In this case, the docker container will not use the version of the MyCHIPs it was built with (in the container's /app folder).
Rather, it will use the MYCHIPS_ROOTNAME variable (defined in build/config.sh) to mount the local repo folder on the docker container at the spot defined by MYCHIPS_DEVDIR.
The container will run the server out of that folder so changes you make to the source code will be used by the container.

In order to use the development method, you will need to also install the WyattERP support libraries as explained in [this section](work-hacking.md).

Note: this method also draws site certificates and the like from the mychips/pki folder
(not local/docker/pki).

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="use-native.md">Next</a>
</div>
