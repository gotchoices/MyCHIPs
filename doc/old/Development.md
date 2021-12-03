## Instructions for Running Reference Code
Dec 2020

### Getting Started
Make, or get into a folder to work in:
```
    mkdir devel; cd devel			#For example
```
If you plan to do any [hacking](#wyatt-hacking) on any of the support libraries, it will be helpful
if this folder will be used only for MyCHIPs.  Otherwise, you can put mychips wherever you like.

Grab the source code from the repository.
If the folder gets created as "MyCHIPs" rather than "mychips" that could
cause some problems on some platforms, so rename it if necessary to "mychips."
```
  git clone https://github.com/gotchoices/mychips
  cd mychips
  npm install				#Install all dependencies
```
Now that the software is installed, you have 3 basic options to give it a try:
- [Docker Test Instance](#docker-test-instance):
  This is probably the easiest option and should work on Linux, Mac or Windows.
  It will also help if you are familiar with [Docker](http://docker.com).
  For Windows users, here are some known issues to be aware of:
  - Make sure docker [can mount your windows volumes](https://docs.docker.com/docker-for-windows/#shared-drives).
  - The "npm run docker" command will make use of the unixy "pwd" command (see inside package.json scripts).
    If you [configure npm to use bash](https://stackoverflow.com/questions/23243353/how-to-set-shell-for-npm-run-scripts-in-windows), this should work correctly.
    Otherwise you may have to execute the docker-compose command manually with the (MYCHIPS_ROOT and MYCHIPS_DIR environment variables set correctly).
  - Git on windows may automatically map UNIX text file LF terminators to CR-LF.
    This will alter certain scripts so the #!shebang command at the top doesn't work right.
    This has been addressed with a .gitattributes file in mychips/bin but if it pops up somewhere else, 
    [this](https://stackoverflow.com/questions/1019946/how-do-i-stop-git-from-adding-carriage-returns-when-cloneing-a-repo-onto-windows) will explain how to configure your git when you clone the repo to avoid this.
  
- [Regular Linux Installation](#regular-linux-installation):
  You will need to install some dependencies and do a little configuration of the environment.
  But for a dedicated server, this is the way to go.
  This should work fine on a Linux VM or a regular installation on physical hardware.

- **Docker Simulation**:
  The docker simulation script allows you to launch any number of MyCHIPs
  server instances in docker containers.  There is also an agent model module 
  that runs on behalf of simulated users to create a data set of random CHIP trades.

  To run the simulation, install Docker on your machine and then get into 
  the test/sim folder and follow instructions in [README.dock](/test/sim/README.dock).

  The simulation environment was developed on MacOS but it should also be 
  possible (though not well tested) to run on a Linux host.
  Not much testing has been done on Windows.
  However at a minimum, you will need to allow docker to mount volumes from your drive as
  [explained here](https://docs.docker.com/docker-for-windows/#shared-drives).

### Docker Test Instance

This is probably the best way to take MyCHIPs for simple testing and evaluation.
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
this with a line in /etc/hosts or C:\Windows\System32\drivers\etc\hosts.
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

### Regular Linux Installation

- Install Postgres, as root:
```
  dnf install postgresql postgresql-server postgresql-devel \
  	postgresql-pltcl postgresql-plpython postgresql-contrib
  dnf install ruby rubygem-pg rubygem-tk	#If you plan to modify the schema
  su -l postgres -c initdb
  systemctl enable postgresql
  systemctl start postgresql
  su -l postgres -c 'createuser -d -s -r admin'
```
- Other known dependencies hopefully installed on your system by default:
  bash, openssl, nodejs, others?

- Checkout MyCHIPs as [noted above](#getting-started).
  After doing the "npm install" do:
```
  npm initcerts				#Initialize local certificates
```

- Next, we will create an admin login ticket.
  This will also build the db schema if it doesn't exist already.
```
  npm run adminticket
```
- Run the mychips server:
```
  npm run server
```
  If you have trouble, set the NODE_DEBUG=debug environment variable
  and watch log files in /var/tmp/mychips
  (Limited testing is also possible without SSL: npm run server -- -n)

- Try connecting to the SPA (possibly from another machine):

  Direct your browser to:  https://<hostname>:8000/admin.html
  
  If connecting over https, your browser should warn you of an insecure site.  
  For testing, you may be able to just proceed anyway.  Better yet, the
  "npm init" command above should have created a certificate in pki/local/spa-ca.crt.  
  If you tell your os/browser you trust that CA, you can proceed without warnings.
  
  See the file in [pki/README.md](../pki/README.md) for more details about securing your site with
  an SSL certificate (whether you use a commercial certificate or make your own).
  
  If the connection is working, you should see an open connection dialog in the 
  upper right corner of the app.

- You will need a ticket to initialize the connection.  In the step above, a
  ticket was created in (by default): test/local/admin.json.
  If it hasn't expired yet, you can use it now.
  
  Otherwise, you need to generate a new one so do that now:
```  
    npm run adminticket			#or:
    npm run adminticket -- -H hostname -P port -o ticket_file.json
```  
  For example, something like:
```
    npm run adminticket -- -H 192.168.56.101 -o test/local/ticket.json	#or
    bin/adminticket mychips.mydomain.com -o test/tmp/ticket.json
```  
  Make sure the host address matches what is on the spa certificate you built
  using the "npm run init" or "npm run cert" commands.
  (See [pki/README.md](../pki/README.md) for more detailed info on this.)
  
- Use the "Import Keys:" option in the connection dialog to open the ticket file.
  You may also drag/drop your ticket file onto the Import button.
  
  Double click on the imported ticket to initiate your connection.
  You should now be prompted for your username (admin).
  The username is purposely not included in the ticket file as a security measure.  
  The user has to know what user the ticket is intended for.
  
  If the ticket is recognized, the GUI should connect to the backend, and promote
  the ticket to a connection key.  Note, the token can only be used once and it
  expires fairly quickly.  If you fail to connect, you may have to issue a new
  ticket (which will automatically invalidate the previous one).  The connection key
  will be good until the admin creates a new connection token for that user.

  The system should next prompt you for a pass-phrase.  This phrase will be used
  when storing your connection key in the browser local storage so others with
  access to your computer can't steal your key.  Leave it blank if you don't want
  to encrypt your key (bad idea in a production environment).

  You should then also export your key and save it in a safe place.  You can
  use this same key in other browsers or to restore your connection if you lose
  or clear your local storage.  If you lose the admin key, you will have to 
  reissue a connection token using the procedure above.  The admin user can issue
  connection tokens for other users using the admin GUI.
  
### URL Tickets:
  It is also possible using the -Q switch to make adminticket produce a URL which
  you can connect to directly, eliminating the need to import a key file into the
  UI as described above.  Something like:
```  
    chrome $(bin/adminticket -Q)
```  
  See the documentation in the wylib package for more detailed information on 
  connection keys.
  
- Now we will add some sample test data to the database:
  Edit the settings file to set IP number of the test machine your database is
  on, and then run the kickstart file.
```  
    cd test
    vi settings.js
    cd sample
    ./kickstart
```
  Reload the user preview in the admin GUI and you should now see 4 users.

- View the live network graph (Network tab)
  See your users on the graph
  Use the graph menu (Upper Right) to Reset or Arrange if necessary

- Add sample tallies/chits (while watching the live Network display)
  Still in test/sample:
```
    psql mychips admin -f tallies.sql
    psql mychips admin -f chits.sql
```  
  Remove them again with
```
    psql mychips admin -c "delete from mychips.tallies"
```
- Add more random users (while still watching the graph)
```
  ./randuser					# or:
  ./randuser -n Number_of_Users_to_Add
```  
  Press Arrange button (or hold it) in graph menu to arrange nodes better

- Launch the agent-model simulator:
```
  cd test/sim
  ./agent
```  
  You can watch as the user nodes will begin to form tallies with each other 
  and begin to trade chits over the tallies.
  
- Lifts
  When the graph accumulates some debits and credits, you can try executing
  some local credit lifts.  Keep in mind, this is not a network simulation
  but only working with a set of users within a single database.
  To work with distributed lifts, see the [docker simulation](../test/sim/README.dock).
  
  To examine the local lift path table, execute this SQL:
```
    select * from mychips.tallies_v_lifts  
```  
  To run a single credit lift, execute this SQL:
```  
    select mychips.lift_cycle(1)		-- Argument = max number of lifts
```

### Want to browse the database schema:

- Launch the mychips server with the -w switch:
```
  npm run server -- -w
```  
- Direct your browser to:	https://<hostname>:8000/wysegi.html

You will need the same admin connection key as was established above for this new connection.
Go to the working admin console, click the server button near the top right, select
your connection key and then "Export keys" from the menu.  This should export
your key to your Downloads folder.  Then go to the Wysegi UI and import that
same key into the server connection dialog.

### Database Logging:

You may want to monitor what postgres is logging.  If so, you may
have to edit pgsql/data/postgresql.conf and set the following:
```
  log_min_messages=notice
```
Consult your local installation for the particular postgres logfile location.
(Something like /var/lib/pgsql/data/log).

### Wyatt Hacking
If you will be working on any of the Wyatt-ERP source code:

- You will need to run the "npm develop" script.  This will remove the four 
  Wyatt modules out of mychips/node_modules.  **It will also expect to find those 
  same modules (wyseman, wylib, wyselib, wyclif) installed in folders at the same level 
  as the mychips folder.**

  So you will have to check these out from github, for example:
```
    cd devel
    git clone https://github.com/gotchoices/wyselib.git
```
  The develop script will run an "npm install" at one level above mychips (in devel)
  which will build an npm_modules folder there and make the required modules 
  accessible to MyCHIPs.
  
  By doing it this way, you are able to edit/change things in the Wyatt code
  and the changes will be immediately accessible to the next run of MyCHIPs.
  
  **Beware:** If you do "npm install" of any kind in the mychips folder, it will
  reinstall the support libraries into node_modules so you won't be running those
  out of the source folders anymore.  You will have to run "npm develop" again to
  clean them out (and restart the server).

### Schema Hacking:
  If you are editing the database schema, you will likely need the following 
  package installations:
```
    dnf install rubygem-pg rubygem-tk gcc-c++
    gem install json
```
  See wyseman/INSTALL for more installation details.

  When MyCHIPs runs for the first time, it will build a stock schema in the
  database if it can't find one.  But you can modify that schema on the fly
  from the sources in the schema folder.  This is done by:
```
    cd mychips/schema
    make objects
```    
  This will also build a few more items in the database for tracking the state
  of the schema (so it knows which objects need to be rebuilt at any given time).
  So it may generate errors on the first run if your schema was 
  instantiated by MyCHIPs (as opposed to this manual build method).

### If you will be working on Wylib:

- Check out the wylib source (if not already done):
```
    cd devel				#For example
    git clone https://github.com/gotchoices/wylib.git
```    
- In the mychips folder, run the "npm develop" script as noted above.
  
- Run a 'watched' build in wylib:
```
  cd wylib
  npm run dev-build
```
- Run a similar build in mychips:
```
  cd mychips
  npm run dev-build
```
- Any changes you make in either the wylib source, or the MyCHIPs source
  will be detected and the packges will be automatically rebuilt.
  You can then just reload your browser to grab the latest changes into the SPA.
  
  If you are making changes to the server-side code, you will have to
  restart the server manually.
  
  It is also possible to run "npm run dev-hot" in the mychips directory.
  This allows you to run the SPA out of port 3000 (rather than 8000).
  **Warning**: This may not always work right if you are making changes to the actions/reports code.

### Testing:

- Run Mocha tests 		(This is done in a separate database)
  Can set NODE_DEBUG=debug (or trace) and observe logs in /var/tmp/mychips
```
  cd devel/mychips/test
```
  Adjust settings in test/settings.js for your environment
```
  npm test				#Or, separately:
  
  npm run test-peercom
  npm run test-impexp
  npm run test-peer

  dropdb mychipsTestDB			#When finished with tests
```  
