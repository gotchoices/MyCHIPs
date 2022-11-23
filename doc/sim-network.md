## Network Simulation

The network simulation (try 2) is implemented by the test/sim/simnet script to launch various 
MyCHIPs services on a number of different machines on your local network.
The goal is to simulate a small working MyCHIPs network environment so as to analyze/implement
the lift algorithm.

This system is not currently maintained and would likely require some effort to make it work
with the current revision server.

Each machine can run:
  - A single postgreSQL instance
  - A single SPA/clif server (currently disabled)
  - Any number of peer servers, each with its own ID, unique to the users
    it services (currently only one implemented)

When the simnet script is run, it will access each configured machine via
ssh and perform the following actions:

  - Grab any changes to the source code so it has the very latest.  This will
    be done via rsync.  We won't use git as there is no guaranty in a testing 
    environment that git will have the latest thing we are working on.
  - Kill any currently running MyCHIPs processes
  - Verify that the machine is properly configured (postgres, node, etc).
    Install/configure any necessary software.
    Make sure the database schema has been initialized
    Note: this only happens on remote machines--not locals (see Config below)
  - Apply any changes to the database schema
  - Relaunch the SPA/clif service (currently disabled)
  - Launch one peer server per site

Since everything is done over ssh, it is very helpful to eliminate the need to 
enter a password each time you connect.  You can do this with:
```
  ssh-keygen -t rsa -b 2048
  ssh-copy-id <username>@<servername>
```
This must be done manually.  It is not done as part of any automated scripting.
You must generate the key one time, and then copy it to each of the machines
you want to access for the simulation.

Most likely you will be connecting to the machines as the root user.  This
measure gives your local machine total control over each of the simulation
machines.  This can create a very big security hole.  So only use machines for
simulation that are not important for other functions.  For example, you can
create a bunch of virtual machines in the cloud that don't really do much
except to run your simulations.

### Configuration
The config.net file in this folder controls how simulations will run.  It 
includes a definition "remotes" which tells the hostnames or IP numbers of the 
machines we will use as hosts for the simulation.  The assumption with remotes 
is they are truly separate machines somewhere on the network.  So when we 
connect, one task is to make sure they are properly configured for running a 
MyCHIPs service (config).  Another important task is to copy any changes of the 
local source tree over to the machine so the instance of the server it will run 
has the "latest greatest" of whatever we are working on.

The config file also contains a definition for "locals."  These are machines
that have direct access to our local source directory (via NFS, or the like).
Typically this will be something like a VM running on our local host.  So for
these machines, we don't attempt to check configuration or sychronize source
code.  We just assume they are properly built/configured and are accessing the 
same source tree so any changes will be realized simply by restarting the 
service.

The configuration file is also able to read a local config file (config.local) 
if it is present.  Anything in config.local should override the defaults in 
config.

### Mongo Database
The simulation uses a separate database to model the "real world" where users
meet independent of the MyCHIPs network protocol.  For example, in the real
world, two users would meet and exchange information via their devices to
facilitate the creation of a tally between them.  In the agent model
simulation, each agent is connected to a single mongo database where agents
are registered and actions are requested of other agents running on other
machines.

So you need to have a mongod running somewhere accessible to the simulation.

### Certificates
Each machine or virtual machine must have appropriate certificates.  For the
simulation, these are drawn from the pki/local folder.  You can initialize a
single machine with the command:
```
  npm run init
```
That works for the machine you are running the command on, but you must also 
generate (at least web) certificates for all the other machines in your 
simulation.  This can be done with something like:
```
  npm run cert -- -t web lux1.%		#Where 'lux1' is a hostname
```
Run this once for each machine in your simulation so the server for that
machine will be able to find it's certificate.  

Keep in mind, these servers are running with self-signed certificates.  You
will have to import the web-ca.crt certificate into your browser (and/or os)
in order to access the admin console without a security warning.

<br>[Next - Local Simulation](sim-local.md)
<br>[Back to Index](README.md#contents)
