<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="use-docker.md">Next</a>
</div>

### Getting Started
First, make (or get into) a folder to work in.  For example:
```
    mkdir devel; cd devel
```
If you plan to do any [programming](work-hacking.md) on any of the support libraries, you may
find it helpful for this folder to be used **only for MyCHIPs.**
Otherwise, you can put the source wherever you like.

The server itself runs in [Node.js](http://nodejs.org) of at least version 18.20.
The environments tested so far are:
- Native Linux on a dedicated server
- Native Linux in a VM (VirtualBox, cloud, etc)
- Docker (which install correct software versions on its own)

If you are developing on a Mac or Windows machine, the server will be running
in a VM or a container so the dependencies listed pertain to that virtual environment--not necessarily the host machine.
You will still need node.js installed on the host but the particular version should not matter as much.

You can check your current node.js version with:
```
  node -v
```
If you need to upgrade, one pretty easy way is:
```
  sudo npm install -g n
  sudo n stable
```

Install the MyCHIPs source code from the [github repository](github.com/gotchoices/mychips) as follows:
```
  git clone https://github.com/gotchoices/mychips
  cd mychips
```
Now that the software is installed, you have 3 basic options to give it a try.
Note: the docker methods will require docker engine >= 20.10.10.
- [Docker Test Instance](use-docker.md):
  This is probably the easiest option and should work under Linux, Mac or Windows.
  But it is not the best path to a production server.
  It will help if you are already familiar with [Docker](http://docker.com).
  For Windows users, here are some known issues to be aware of:
  - Make sure docker [can mount your windows volumes](https://docs.docker.com/docker-for-windows/#shared-drives).
  - The "npm run docker" command may make use of certain unixy commands (see inside package.json scripts).
    If you [configure npm to use bash](https://stackoverflow.com/questions/23243353/how-to-set-shell-for-npm-run-scripts-in-windows), this should work correctly.
    Otherwise you may have to execute the docker-compose command manually (with the various required environment variables set correctly).
    Some Windows users have better success running things in the [git bash shell](https://gitforwindows.org/).
  - Git on windows may automatically map UNIX text file LF terminators to CR-LF.
    This can alter certain scripts so the #!shebang command at the top doesn't work right.
    Hopefully, this has been addressed with a .gitattributes file in mychips/bin but if it pops up somewhere else, 
    [this](https://stackoverflow.com/questions/1019946/how-do-i-stop-git-from-adding-carriage-returns-when-cloneing-a-repo-onto-windows) explains how to configure your git when you clone the repo to avoid this.
  
- [Regular Linux Installation](use-native.md):
  You will need to install some dependencies and do a little configuration of the environment.
  But for a dedicated server, this is the way to go--at least for now.
  This should work fine on a Linux VM (such as VirtualBox) or a regular installation on physical hardware.

- [Docker Simulation](sim-docker.md):
  There are several simulation environments located in the test/sim directory.
  The latest version, based on docker, allows you to launch a number of MyCHIPs
  server instances in docker containers.  There is also an [agent model](sim-agent.md) module 
  that runs on behalf of simulated users to create a data set of random CHIP trades.

  To run the simulation, install Docker on your machine and then get into 
  the test/sim folder and follow the instructions [here](sim-docker.md).
  The current simulation Model 3 docs are found [here](../lib/model3/doc/README.md), and contain a summary of the instructions and implementation details. We suggest referring to Model 3 docs first when trying to run the most current version of the simulation.

  The simulation environment (mostly shell scripts) was developed on MacOS but it should also be 
  possible (though not well tested) to run on a Linux host.
  Not much testing has been done on Windows but it may work with some care and effort.

<div style="display: flex; justify-content: space-between;">
  <a href="README.md#contents">Back to Index</a>
  <a href="use-docker.md">Next</a>
</div>
