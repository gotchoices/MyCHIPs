### Docker Test Instance

This is probably the quickest way to launch MyCHIPs for simple testing and evaluation.
You will need docker and node/npm installed on your system.

To launch a single server/database pair:
```
  npm run docker
```
This will take a while on first run as it builds several images.  It will be 
faster on subsequent runs.  Once containers are launched, it will run until you 
interrupt it with a CTRL-C.

The server is configured from the file build/config-dev.env.  By making
multiple such configuration files, you should be able to launch multiple
instances of the server pair.  Keep in mind, the hostname you choose for the 
MyCHIPs server will have to resolve to your system.  For testing, you can solve 
this with a line in /etc/hosts (or C:\Windows\System32\drivers\etc\hosts.)
```
  127.0.0.1	mychips0
```
This hostname is what we will be entering into the browser URL bar to get the 
admin app.  It is also what will be built into the SSL certificates so
everything has to use the same hostname for the browser to be happy over https.

Once the server pair is running, we would like to connect to it using the admin UI.
But the backend will not allow this without an authorized connection token.
You can create one using the following bootstrap command:
```
  docker exec mychips0 bin/adminticket -S 8000 -P 54320 -H mychips0 -Q
```
The https SPA (Single Page Application) port and WebSocket ports in this command 
must match up with what is in the config-dev.env file for the server pair you just launched.
The bootstrap command will output a URL (containing the connection token) which 
you can copy/paste into your browser.  Or if you are really tricky you can do 
it all in one step with something like this (on Mac OS):
```
  open -n -a Firefox.app --args -new-tab \
    $(docker exec mychips0 bin/adminticket -S 8000 -P 54320 -H mychips0 -Q)
```
Next, the browser will complain that you are connecting to an SSL web server 
using a certificate signed by an unknown certificate authority.
To fix that, you can import the CA file created by the software as follows (again for Mac OS):
```
  open test/local/docker/pki/spa-ca.crt
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

<br>[Next - Native Installation](use-native.md)
<br>[Back to Index](README.md#contents)
