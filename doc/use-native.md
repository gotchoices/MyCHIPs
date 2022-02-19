## Regular Linux Installation

The core of MyCHIPs is implemented in Postgres so you will have to install that package.
In a production environment, you may well be installing Postgres on a 
[separate server](use-pki.md)
but getting that running correctly is beyond the scope of this document.
So unless you know what you are doing, just put it on the same server for now.

Most testing has been done on Fedora Linux (up through version 35).
MyCHIPs should work on other Linux distributions, but you may have to adapt these
instructions accordingly.

As root:
```
  dnf install postgresql postgresql-server postgresql-devel \
  	postgresql-pltcl postgresql-plpython3 postgresql-contrib
  dnf install ruby rubygem-pg rubygem-tk	#If you plan to modify the schema
  su -l postgres -c initdb
  systemctl enable postgresql
  systemctl start postgresql
  su -l postgres -c 'createuser -d -s -r admin'
```
Other known dependencies (hopefully installed on your system by default) include:
```
  bash, openssl, nodejs, others?
```
Checkout MyCHIPs and install as [noted here](use-start.md#getting-started).
After doing the "npm install" step do:
```
  npm initcerts				#Initialize local certificates
```
This will create some temporary certificates suitable for testing.
For production use, you will need to make real certificates as mentioned below.

Next, we will create an admin login ticket.
This will also initialize the database schema if it doesn't exist already.
```
  npm run adminticket
```
Now launch the mychips server:
```
  export NODE_DEBUG=debug
  npm run server
```
  The NODE_DEBUG variable will cause the server to put logging information
  in /var/tmp/mychips so you watch its progress with:
```
   tail -f /var/tmp/mychips/combined.log
```

<br>[Next - Connecting the Admin UI](use-admin.md)
<br>[Back to Index](README.md#contents)
