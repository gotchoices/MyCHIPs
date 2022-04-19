## Local Simulation

This was the first attempt at MyCHIPs simulation.
All it really does is allow one to launch a set of server instances from
a series of shell windows.  It does not implicitly include any kind of
agent model or other function to stimulate transactions between the servers.

These scripts have not been maintained for several years and will likely require
some effort to make them work correctly with the current system.

They may come in handy again at some point in order to debug certain situations
in the peer-to-peer protocol so we will keep them around for now.

This consists of two scripts, both located in the test/sim directory:

- simlocal:
  Runs a specified number of instances of the server on the local (Linux) machine.
  You will need some additional mechanism for initiating a transacton between
  the instances.

- watchlogs: (calls watchalog)
  Launches a terminal window to monitor each of the servers created from the 
  simlocal command.

<br>[Next - Agent Based Model](sim-agent.md)
<br>[Back to Index](README.md#contents)
