## Regular Linux Installation

The MyCHIPs model is implemented in PostgreSQL so you will have to install that package.
In a production environment, you may be installing it on a [separate server](use-pki.md)
but doing so is beyond the scope of these instructions.
If you don't know how to get that working correctly, just install it on the same server for now.

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
After doing the "npm install," you may want to enable debugging mode as follows:
```
  export NODE_DEBUG=debug
```
  This will cause the server to write logging information in /var/tmp/mychips (or such other
  place as may be configured) so you watch the server progress with this command:
```
   tail -f /var/tmp/mychips/combined.log
```
Next initialize your local site certificates using the following interactive command.
(You may skip this step and the system should create a very generic site certificate good enough for basic testing.)

```
  npm run initcerts
```
Then you can launch the MyCHIPs server with:
```
  npm run start
```
This will:
- create some temporary certificates suitable for testing (if you didn't run initcerts manually as above),
- initialize a default user agent ID, and
- launch the MyCHIPs server.
For production use, you will need to make real certificates and agent IDs as explained [later](use-pki.md).

<br>[Next - Connecting the Admin UI](use-admin.md)
<br>[Back to Index](README.md#contents)
