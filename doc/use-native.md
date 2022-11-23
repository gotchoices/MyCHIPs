## Regular Linux Installation

The MyCHIPs core model is implemented in PostgreSQL so you will have to install that package.
In a production environment, you might be installing it on a 
[separate server](use-pki.md#database-certificates) which  is beyond the scope of these instructions.
If you don't know how to get that working correctly, just install it on the same server for now.

Most testing has been done on Fedora Linux (up through version 35) and Ubuntu (through 22.04).
MyCHIPs should work on other Linux distributions, but you may have to adapt these
instructions accordingly.

## Automated Build
The distribution now includes a set of experimental build scripts which are intended
to fully configure a system such as might be build on a cloud service.
To use it, follow these steps:
- Build a cloud server
- Select the OS as Ubuntu (22.04 tested)
- Point your DNS service to the newly created server IP
- Establish key-based ssh connection for root to the server as follows
```
  ssh-copy-id root@Server-Domain-Name		(or use the IP number)
```
- While still on your development machine (not the new server) do:
```
  cd mychips/build/host
  ./setup -i New_Server_IP -d New_Server_Domain_Name
```
There is a lot of logging that goes by.  If you're not sure, it should
be safe to run the script again and it should skip over steps that seem
to be already done.

If everything worked perfectly, you may have a new, running server.
If not, you may need to refer to the next section for help.

One advantage of the automated build is it is geared to install real
certificates for your site using [certbot](https://letsencrypt.com).
The procedure in the next section uses only self-signed certificates.

## Building By Hand
As root:
```
  dnf install postgresql postgresql-server postgresql-devel \
  	postgresql-pltcl postgresql-plpython3 postgresql-contrib
  su -l postgres -c initdb
  systemctl enable postgresql
  systemctl start postgresql
  su -l postgres -c 'createuser -d -s -r admin'
```
Here is a comparable installation sequence for Ubuntu:
```
  apt-get update
  apt-get install - postgresql postgresql-contrib \
        postgresql-pltcl postgresql-plpython3
  service postgresql enable
  service postgresql start
  su -l postgres -c 'psql -c "create role admin with login createdb superuser createrole"'
```
You will also have to configure PostgreSQL to accept connections from the local
machine (or the machine mychips is running on).  
[This document](https://www.postgresql.org/docs/current/auth-pg-hba-conf.html)
should get you going for simple cases.
If your machine is well locked down and has only a single user to launch the mychips server
it should be safe enough to use the trust authentication method.

Other known dependencies (hopefully installed on your system by default) include:
```
  bash, openssl, nodejs, others?
```
Checkout MyCHIPs from github and install as [noted here](use-start.md#getting-started).
After doing the "npm install," you may want to enable debugging mode as follows:
```
  export NODE_DEBUG=debug
```
  This will cause the server to write logging information in /var/tmp/mychips (or such other
  place as may be configured) so you watch the server progress with this command:
```
   tail -f /var/tmp/mychips/combined.log
```
You can now initialize local self-signed site certificates using the following interactive command.
(If you skip this step, the system will create a very generic site certificate good enough for basic testing.)

```
  npm run initcerts
```
Then you can launch the MyCHIPs server with:
```
  npm start
```
This will:
- Create some temporary certificates suitable for testing (in case you didn't run initcerts manually as above),
- Initialize a default user agent ID, and
- Iaunch the MyCHIPs server.
For production use, you should likely make real certificates and agent IDs as explained [later](use-pki.md).
This will avoid the need for your users to install your self-signed site CA.

<br>[Next - Connecting the Admin UI](use-admin.md)
<br>[Back to Index](README.md#contents)
