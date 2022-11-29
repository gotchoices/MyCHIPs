### Docker Test Instance

This is a quick and simple way to launch MyCHIPs for simple testing and evaluation.
You will need docker and node/npm installed on your system.
Also, this is easier on Mac and perhaps Windows as docker under Linux 
has certain additional [permission issues](https://docs.docker.com/engine/install/linux-postinstall/).

To launch a single server/database pair in development mode:
```
  npm run docker-dev
```
This will take a while on first run as it has to build images.  It should be 
faster on subsequent runs.  Once containers are launched, it will run until you 
interrupt it with a CTRL-C.  You can then use this to stop and remove the
containers:
```
  npm run docker-stop
```
Beware, the container needs to mount the mychips main directory.
If this is not called "mychips" (i.e. MyCHIPs) make sure you set the environment 
variable MYCHIPS_ROOTNAME as needed by build/compose-dev.yml.

The server is configured from the files build/config-dev.env and
build/compose-dev.yaml.  Keep in mind, the hostname you choose for the 
MyCHIPs server will have to resolve to your system.  For testing, you can solve 
this with a line in /etc/hosts (or C:\Windows\System32\drivers\etc\hosts.)
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

### Development Docker Caveats
In order to allow development work, the compose-dev.yaml file totally
ignores the static copy of the mychips app built into the image
(in the /app directory).
Instead it mounts a live copy of the host systems mychips filesystem on the container.

Specifically, it mounts whatever directory you have *mychips installed in*
on /usr/local/devel.  This implies that anything else you have installed in the same
folder is also accessible to the container.  This is so you can install the
WyattERP suite parallel to mychips (rather than running out of node_modules).
This allows you to work on those packages and have the changes seen immediately in
your running container.

See [this section](work-hacking.md) for more on how to do this.

This compose file also draws site certificates and the like from the mychips/pki folder
(not local/docker/pki).

### Production Docker Container
There is also a build profile for running a production docker instance that
can be launched as follows:
```
  npm run docker
```
This is not currently well tested.  Hopefully that will become better developed in the 
future so one can run a development server under docker.

If you experiment with this version, note that keys/certificates are accessed from
the folder: test/local/docker/pki.

<br>[Next - Native Installation](use-native.md)
<br>[Back to Index](README.md#contents)
