## Connecting the Admin UI

Once you have a MyCHIPs server running, you can try connecting to the 
SPA (possibly from another machine) by directing your browser to:
```
https://<hostname>:8000/admin.html
```
  Your browser will likely warn you of an insecure site.  
  For testing, you may be able to just proceed anyway.  Better yet, the
  "npm init" command above will have created a certificate in pki/local/spa-ca.crt 
  (or test/docker/pki/spa-ca.crt for a docker test instance).
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
  
### Testing the Server
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

<br>[Next - User Application](use-pki.md)
<br>[Back to Index](README.md#contents)
