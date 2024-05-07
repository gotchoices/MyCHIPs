<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="work-testing.md">Next</a>
</div>

## Working on the Software

### WyattERP Hacking
If you will be working on any of the Wyatt-ERP source code, you will need to check out copies of the WyattERP support libraries as follows:
```
    cd MyCHIPs/..
    git clone https://github.com/gotchoices/wylib.git
    git clone https://github.com/gotchoices/wyseman.git
    git clone https://github.com/gotchoices/wyselib.git
    git clone https://github.com/gotchoices/wyclif.git
```
You will also need the ChipNet suite as follows:
```
    cd MyCHIPs/..
    git clone https://github.com/gotchoices/chipcrypt.git
    git clone https://github.com/gotchoices/chipcryptbase.git
    git clone https://github.com/gotchoices/chipcode.git
    git clone https://github.com/gotchoices/chipnet.git
```

By default, any running of "npm install" in the mychips folder will attempt to install versions of these package in node_modules (from npmjs.org), which is not what we want here.

We will run the "npm develop" command (or bin/develop) to configure MyCHIPs to access these libraries from local source rather than installing from npmjs.org.

Specifically, bin/develop will
- remove the support modules out of mychips/node_modules; and then
- move to the folder above MyCHIPs (devel); and then
- install each of the libraries as in this example:
```
   npm install wyseman/		#for example
```
The script expects to find the specified packages installed in folders at the same level as the MyCHIPs folder.
This installation process will also create a node_modules folder above MyCHIPs which will be accessed to find the packages.

Once set up in this way, you are able to edit/change things in the support libraries
and the changes will be immediately accessible to the next run of MyCHIPs (even in a development mode docker container).
  
**Beware:** If you do "npm install" or "npm update" in the mychips folder, it will
reinstall the support libraries (from npmjs.org) into node_modules so you won't be running those
out of the source folders anymore.  You will have to:
- run "npm develop" again to clean them out; and
- restart the server.

### Schema Hacking
If you are editing the database schema, you will need access to the wyseman package
(whether installed from npmjs.org or in a local source folder).
See wyseman/INSTALL for more installation details and dependencies that may be required.

When MyCHIPs runs for the first time, it will check for the existence of a "mychips" database.
If it doesn't find one, it will create a new one.
It is also possible to modify the schema on the fly from the sources in the schema folder.
This is done by:
```
    cd mychips/schema
    make objects
```

See the wyseman documentation for more information on schema maintenance.

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

Note: there is also a similar tool available now in the Database tab of the admin web UI.

### Database Logging:

You may want to monitor what postgres is logging.  If so, you may
have to edit pgsql/data/postgresql.conf and set the following:
```
  log_min_messages=notice
```
Consult your local installation for the particular postgres logfile location.
(Something like /var/lib/pgsql/data/log).

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="work-testing.md">Next</a>
</div>
