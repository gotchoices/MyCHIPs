## Brief description of what is in the various folders:

### bin
Things you would execute from the command line on the hosting computer.
This may end up being limited to the MyCHIPs server as it is turning out to 
encompass all the different functionality within a single program.

### contract
MyCHIPs tokens are not stand-alone coins as with Bitcoin.  Rather, a CHIP
is an agreement between two parties.  So instead of being based on the
notion of authority, it is based on mutual consent between two willing
participants.
    
As such, it becomes necessary to define the terms of the agreement.  CHIP
trading partners can choose a satisfactory contract by which they will
conduct their credit dealings.  
    
The source language for these contracts is kept here.

### doc
Package documentation.  Also includes:
  - doc/Notes: the author's originalhand sketches, notes and computations
  - doc/Projects: specifications for potential coding projects to further
    the system's development.

### lib
Contains modules that are required by the MyCHIPs server.
Functionality includes:
  - A web server to serve up user and admin SPA's described below
  - A web server to serve up contract documents
  - Communication with the site administrator
  - Communication with a mobile user agent
  - Communication with peer users' servers
  - Interaction with the database

### src
Contains code for the admin and user SPA.  These applications run in a
browser to allow the administrator and MyCHIPs user to access the
relevant data and functions of the server and database.  
    
### pub
Contains webpack bundles of the SPAs.  The web server points here as its
base folder to serve up the SPA applications.
    
### schema
Contains a definition of the database schema, authored and maintained in 
the Wyseman format.  This means, source files are written as TCL 
structures which contain SQL fragments, macros and shortcuts which will
ultimately produce the full SQL required to build the schema.
    
A database can be instantiated by entering this directory and executing
"make all."  This is more of a development approach.  More commonly, the
database will get built by the first invocation of the server, which will
detect that the required tables are not present, and so will build it
according to the compiled SQL file (in lib) which is derived from the
Wyseman sources in this folder.

### test
Contains mocha tests as well as a variety of sample data for use in
development.
    
The test/sim folder contains several simulation environments.  The most
recent of which is "simdock" which spins up any number of instances of 
sites and servers in docker containers to simulate a real network.  This 
can be used in conjunction with the agent-based model to create distributed 
data sets for testing and validation.

<br>[Next - Known Issues](ref-bugs.md)
<br>[Back to Index](README.md#contents)
