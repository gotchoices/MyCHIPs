## MyCHIPs Simulations

The folder test/sim contains several different iterations of simulators.
The main idea is to launch the production server program multiple numbers of times
along with a number of bot processes that attempt to act like human beings might
an economy of CHIP traders.

The simulations are helpful in creating data sets for analyzing the MyCHIPs
protocol or for analyzing economic outcomes in the network.

## Containerized Simulation

Simdock (try 3) is a re-implementation of the simnet (try 2) script where, instead of running on
separate virtual machines, all processes are launched as docker containers.
Most functionality is wrapped inside the test/sim/simdock script.

Simdock has less memory overhead than the earlier simnet implementation so a
single system can support the simulation of more sites. However it is still
quite CPU intensive so things can run slow if you are modeling lots of sites.

Hopefully this docker-based simulation can be enhanced and extended to launch
many containers in the cloud for a much larger-scale simulation.

The simulation keeps run-time data in a subdirectory of this folder called
'local.' For example, all instances of the postgres database directory get
created there. Also, all MyCHIPs logfiles get created there. This gives a
single place for monitoring the status of a running simulation.

Under the earlier simnet implementation, multiple VMs were created and each VM
represents a "site" and so would typically have an instance of the postgres
database, an SPA server, a peer server, and an agent modeler. The idea is, a
site represents a single MyCHIPs service provider and its customers.

In this docker-based version, each process is a separate container. So the
notion of a "site" is not quite as clear. It is probably best to think of a
site as an "instance of postgres" plus a few other processes (SPA, peer and
agent) that are part of that logical site but run in their own containers.
This may be how some larger-scale service providers might operate anyway--with
different processes running on different servers, all a part of the same site.

In addition to sites, there are two additional containers. The mongo container
is just as in the simnet case: a database to represent the "real world" where
agents meet each other and exchange information outside the MyCHIPs network.
It is not a part of the production software but is used only as part of the
simulation.

There is also a "devel" container which contains a Fedora machine primarily
used for development tasks such as updating the database schema in between runs
of the simulation (say, in the case where you have made schema programming
changes). You can launch a shell on the devel container to examine the
simulation network from the perspective of a machine on that network.

The devel container can also backup and restore all your databases to a named
profile (see command examples below). This allows you to save a certain state
for later analysis or debugging.

To get started, run the following commands (from this directory):

```
  export PATH="$(pwd)/../../node_modules/.bin:$PATH"
  export NODE_DEBUG=debug
  ./simdock startup
```

This should fetch and build the necessary docker images (which can take quite a
long time). Next, it will launch the mongo and devel containers. It will then
launch a number of sites, equivalent to running "simdock start sites" manually.  
This can take a while the first time you run because it has to initialize a
database for each site.

This step also includes opening a bunch of xterms (or the local logwin script
for Mac) on your screen to view the logfiles. NOTE: MacOS is discontinuing
support of tcl/tk (wish). Version 10.15 (Catalina) is already showing
instabilities that make logwin unstable. If you are having a problem with
logwin on Mac, it should help to install wish from homebrew (https://brew.sh/)
using (make sure new wish is also in your path):

```
  brew install tcl-tk
```

If things still don't work right (like your screen is smaller than 1920 pixels,
for example) now is a good time to check out the configuration file: config.dock.

If you want to change configuration items, make a similar file in the "local"
subdirectory:

```
  local/config.dock
```

and put in there whatever settings you want to modify from the config.dock in
this folder. Some good things to focus on include:

```
  agentwins, peerwins, spawins #X,Y screen coordinates of logging xterms
  logoffset                    #How xterms are tiled on the screen
  browser                      #Only firefox/chrome tested for now
  logwin                       #If you want to use xterm instead of logwin
  newusers                     #How many users to create on each site
  sites                        #How many sites to launch on simulation runs
  userargs                     #Additional command line switches to docker
                               run command.  For example, you could make each
                               container's bash run your preferred settings:
  userargs=( '-v' "$HOME/.bashrc:/root/.bashrc" )	#Custom bashrc, key mappings
```

If you have made changes, shut things down using:

```
  ./simdock shutdown
```

And then start it back up again with:

```
  ./simdock startup
```

You can check your running containers with:

```
  docker ps
```

You should see a mongo, a devel, and N instances of postgres and the SPA server.
You should have N xterms on your screen showing the logs of the running SPA
servers. There should be another set showing the postgres logs. Make sure
those servers get initialized and launched all the way before launching the
UI's as noted below.

Next, you will need to put some aliases in your /etc/hosts (or other DNS
mechanism) to resolve the hostnames we will use in the simulation. Your
browser will be connecting to a docker hostname which needs to resolve to
the local host where docker ports will get mapped. But the hostname in the
browser URL bar needs to match what is in the SSL certificates, so you will
need to have hostnames in /etc/hosts that actually just resolve to your
local IP. For example:

```
  127.0.0.1	spa0 spa0.mychips.sim
  127.0.0.1	spa1 spa1.mychips.sim
  127.0.0.1	spa2 spa2.mychips.sim
  127.0.0.1	spa3 spa3.mychips.sim
```

OK, now make sure you have a browser (firefox,chrome) window running and do:

```
  ./simdock tickets
```

This should generate connection tickets for each of the running SPA servers
and launch a browser tab for the admin console of each, using the applicable
ticket. At this point, you may well get a security warning because you are
connecting via https to a node with a self-signed CA. Look for a CA
certificate in:

```
  test/sim/local/pki/spa-ca.crt
```

and install it in your browser (and/or OS).

On MAC and Windows, you should be able to double click on the file to install
the certificate. You will then have to find and adjust the setting to trust
all certificates signed by this authority.

Note: Firefox requires you to set the value security.enterprise_roots.enabled
to true (in about:config) in order to read certificate information from the OS.
Firefox probably also needs to be restarted.

Once you get all that sorted out, rerun the "simdock tickets" command and see
that the admin console is successfully connecting to each of the running SPA
servers.

Note that, as with most plural (like "tickets") commands in simdock, you can
also do:

```
  ./simdock ticket 2
```

to launch a single admin console (to site 2 in this case).

Last setup step is to rebuild all the database objects from scratch. The
default MyCHIPs server will build a pre-compiled schema by default. But we
may want the simulation to run from our source folder so if you tweak the
schema, you will see the effect of the change in the simulation. Additionally,
this will update the database with some helpful configuration settings, such as
default host names and ports.

This actually gets done automatically (if the schema has changed) with each
simulation run, but the first time, it can be a little more clear to run it
explicitly. Keep in mind, this can also take a while when run for the first
time. And in some instances it can fail on the first run so you may have to
try it twice:

```
  ./simdock dbcheck all
```

Finally, it's time to start the simulation. Run this:

```
  ./simdock start sim --runs=50
```

This should launch two more sets of logging windows on your screen (hopefully
your local/config.dock settings are working OK). It will also launch two more
container processes for each site, a peer server and an agent modeler. The
peer server is the production MyCHIPs server that handles traffic from other
servers on the network. The agent modeler attempts to simulate what humans
might do when interacting on a MyCHIPs network (trading CHIPs in transactions).
This command tells the agent modeler to run 50 iterations of its simulation.

If your admin consoles are connected, you can select the Network tab to see
tally connections being formed in the simulated network. There is an "Arrange"
function in the graph menu near the upper right that will help arrange the
nodes on the screen.

To kill the simulation, do:

```
  ./simdock stop sim
```

This will issue shutdown commands to the applicable containers. However it
will take some time for them all to shut down. The script exits quickly, but
you will see a confirmation some seconds later in the terminal as each container
actually shuts down. You can run a "docker ps" to make sure they are gone before
re-launching.

Finally, this command should kill any/all containers related to the simulation:

```
  ./simdock shutdown
```

Keep in mind, if you launched the simulation with sites set to 6 and then
changed the configuration to 4 before doing the shutdown command, not all your
containers will get killed. You may have to do that manually.

###Command Examples

```
  export NODE_DEBUG=debug
  ./simdock startup               #Run mongo/development/PG/SPA containers
  ./simdock dbcheck all           #Update the database schema from source
  ./simdock tickets               #Connect to SPA servers via browser
  ./simdock start sim --runs=50   #Run simulation
  ./simdock stop sim              #Stop simulation
  ./simdock shutdown              #Stop everything

  ./simdock init                  #Reset users/peers/tallies to start values

  ./simdock start pg 0            #Start the first postgres
  ./simdock start pg all          #Start all postgres containers
  ./simdock start spa all         #Start all SPA servers
  ./simdock start site 1-3        #Start postgres and SPA servers 1 through 3
  ./simdock -s=10 start sites     #Start sites 0-9
  ./simdock stop pg 0             #Stop the first postgres
  ./simdock stop pg0              #Ditto (but only works for stop, not start)
  ./simdock stop pg all           #Stop all postgres containers
  ./simdock stop pg 2-4

  ./simdock start peer all        #Start all peer servers
  ./simdock start peers           #Ditto
  ./simdock start agents --runs=10    #Run agents to do 10 iterations
  ./simdock stop agents           #Stop all agents

  ./simdock start mongo           #Start mongodb (public database)
  ./simdock stop mongo            #Stop mongodb

  ./simdock dbcheck 0 -f          #Rebuild the database even if the schema doesn't appear to have changed since last build
  ./simdock backup all profile1   #Backup all DB's to a folder called profile1 (stop spas,peers,agents first)
  ./simdock dropdb all            #Drop all databases (run this prior to a restore)
  ./simdock restore all profile1  #Restore all DB's from a folder called profile1
```

## Development on Agent 3 with Typescript

The Agent 3 simulation model is developed with TypeScript. Therefore, if any changes are made to the TypeScript files (\*.ts), then they must be transpiled to JavaScript before the simluation can run using Agent Model 3.

1. Edit \*.ts files
2. Run the TypeScript transpiler CLI by using the following script:

   ```
   npm run tsc
   ```

3. Make sure to set V3 agent model in test/sim/local/config.dock
   ```
   agentversion=3
   ```
4. Follow steps above to run simulation

<br>[Next - Network Simulation](sim-network.md)
<br>[Back to Index](README.md#contents)
