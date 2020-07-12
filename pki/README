All files here in subject to:
Copyright MyCHIPs.org; See license in root of this package
-----------------------------------------------------------------------------

This folder contains recipes for creating self-signed certificates.  We will
use such certificates in three separate instances:

  - To validate the connection between the MyCHIPs server and a client Single 
    Page Application (SPA) such as the admin console, user console, or a user 
    mobile app.
  - To validate the connection between the MyCHIPs server and the PostgreSQL
    server.
  - To validate the connection between peer MyCHIPs servers (not implemented).

For a more detailed version of these instructions, generic to WyattERP, see:
 
  node_modules/wyclif/pki/README

and where generic naming is applicable, assume 'mychips' instead of 'wyclif' or
'wyatt.'

--------------------------------------------------------------------------------
To make SPA certificates:			#Quick start

  cd mychips/pki
  cp example.conf local.conf			#Create your own local config
  $EDITOR local.conf				#Modify it for your own site

  npm run cert -- -t spa <servername.%>

Where "servername" is the name of the computer your server is running on.

There is a file called spa-ca.crt which you will have to install in your
browser and/or OS to tell it our certificates can be trusted.
  
--------------------------------------------------------------------------------
To Make Database Certificates			#Quick start

This may not be necessary in all configurations.  Where needed, you will also
need to configure your postgreSQL server. 

See wyclif/pki/README for details on this.

For an SSL-secured connection, we will create keys as follows:

  npm run cert -- -t data <servername.%>
  npm run cert -- -t data admin
  npm run cert -- -t data users

--------------------------------------------------------------------------------
To Make Peer Certificates

  npm run cert -- -t peer <servername.%>

Peer certificates are not a part of standard Wyclif/WyattERP but are an
extension specifically for MyCHIPs.  The server will automatically find the
certificate built by this method if you named it the same as your server name.

If not, you may have to supply a command line switch or environment variable in
order for the server to find it correctly.  See bin/mychips.js for switches and
variable names.
