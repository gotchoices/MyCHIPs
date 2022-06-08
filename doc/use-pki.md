## Public Key Infrastructure

The pki folder contains recipes for creating self-signed certificates.
You can create certificates to:
  - validate the connection between the MyCHIPs server and a client Single 
    Page Application (SPA) such as the admin console, user console, or a user 
    mobile app.
  - validate the connection between the MyCHIPs server and the PostgreSQL
    server.

For a more detailed version of these instructions, generic to WyattERP, see:
```
  node_modules/wyclif/pki/README
```
and where generic naming is applicable, assume 'mychips' instead of 'wyclif' or 'wyatt.'

### SPA Certificates
This is done automatically for test purposes when you use the initcerts script.
But you will want to make a more customized certificate for production use.
To make SPA (Single Page Application) certificates:
```
  cd mychips/pki
  cp example.conf local.conf			#Create your own local config
  $EDITOR local.conf				#Modify it for your own site

  npm run cert -- -t spa <servername.%>
```
Where "servername" is the name of the computer your server will be running on.

There is a file called spa-ca.crt which you will have to install in your
browser and/or OS to tell it our certificates can be trusted.
  
### Database Certificates
This may not be necessary in all configurations.
Where needed, you will also need to configure your postgreSQL server. 

See wyclif/pki/README for more details on this.

For an SSL-secured connection, we will create keys as follows:
```
  npm run cert -- -t data <servername.%>
  npm run cert -- -t data admin
  npm run cert -- -t data users
```

### Agent ID's
An agent can be thought of as that process that handles transactions for a particular user or group of users.
There can be one or many agents associated with a single database instance.
You can learn more about agents in the section on [CHIP addresses](learn-users.md#chip-addresses).

The site administrator may need to create one or more agent addresses for each site.
When you run the npm start script, the system automatically calls another script that checks to make sure there is at least one agent ID defined
and one agent set as the default.

This can be invoked manually with one of the following:
```
  npm run agentcheck
  bin/agents check
```

You can list currently defined agents using one of:
```
  bin/agents list
  bin/agents ls
```

You can delete an existing agent using one of:
```
  bin/agents rm <agent_ID>
  bin/agents remove <agent_ID>
  bin/agents del <agent_ID>
```

You can create a new agent using one of:
```
  bin/agents new
  bin/agents add
```

Creating a new agent simply produces a new noise protocol private key and stores it in the pki/local folder.
If you want to use any agent (other than the default) you will have to write it to the applicable field
in the mychips.users_v view for each user who is expected to be reachable at that agent address.

Users who have no agent setting will be reachable at whatever the default agent setting is.
The default agent is simply specified by a symbolic link in the pki/local folder called "default_agent".

<br>[Next - System Administration](use-mobile.md)
<br>[Back to Index](README.md#contents)
