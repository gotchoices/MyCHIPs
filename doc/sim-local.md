## Local Simulation

This was the first attempt at MyCHIPs simulation.
It is pretty crude but probably worth keeping around for now.

It consists of two scripts, both located in the test/sim directory:

- simlocal:
  Runs a specified number of instances of the server on the local machine.
  This is good for simple simulations like testing the state transitions for 
  peer dialogs.

- watchlogs: (calls watchalog)
  Launches a terminal window to monitor each of the servers created from the 
  simlocal command.

<br>[Next - Agent Based Model](sim-agent.md)
<br>[Back to Index](README.md#contents)
