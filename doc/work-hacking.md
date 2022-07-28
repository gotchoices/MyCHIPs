## Working on the Software

### WyattERP Hacking
If you will be working on any of the Wyatt-ERP source code:

You will need to run the "npm develop" script.  This will remove the four 
Wyatt modules out of mychips/node_modules.
- Wylib
  A library that runs in a browser-based UI client to interface with a 
  Wyseman-baserd backend server.
- Wyseman
  Provides the server side of the API to communicate with Wylib-based apps.
  Includes a schema management application for tracking and deploying
  changes and updates to the PostgreSQL database schema.
  Also provides non-web (JS, Ruby, Dart) client-side modules.
- Wyselib
  A library of schema objects to implement a basic ERP.
  More specialized apps can be built on top of this base schema.
- Wyclif
  Generic support modules for building the server-side of an application.

**The develop script will expect to find these four modules installed in folders 
at the same level as the mychips folder.**

So you will have to check these out from github, for example:
```
    cd devel
    git clone https://github.com/gotchoices/wylib.git
    git clone https://github.com/gotchoices/wyseman.git
    git clone https://github.com/gotchoices/wyselib.git
    git clone https://github.com/gotchoices/wyclif.git
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

### Schema Hacking
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

### Working on Wylib

Enter development mode as described [above](#wyatterp-hacking)
  
You can then run a 'watched' build in wylib.
```
  cd wylib
  npm run dev-build
```
Then run a similar build in the mychips directory:
```
  cd mychips
  npm run dev-build
```
Any changes you make in either the wylib source, or the MyCHIPs source
will be detected and the packges will be automatically rebuilt.
You can then just reload your browser to grab the latest changes into the SPA.
  
If you are making changes to the server-side code, you will have to
restart the server manually.  Something like:
```
  npm run server
```
It is also possible to run "npm run dev-hot" in the mychips directory.
This allows you to run the SPA out of port 3000 (rather than 8000).
However, this may not always work right if you are making changes to the
control layer (actions/reports) code.


### Browsing the Database Schema
Launch the mychips server with the -w switch:
```
  npm run server -- -w
```  
Direct your browser to:	https://<hostname>:8000/wysegi.html

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

<br>[Next - Testing Environment](work-testing.md)
<br>[Back to Index](README.md#contents)
