### Getting Started

First, make (or get into) a folder to work in:
```
    mkdir devel; cd devel			#For example
```
If you plan to do any [programming](work-hacking.md) on any of the support libraries, you may
find it helpful for this folder to be used **only for MyCHIPs.**
Otherwise, you can put the source wherever you like.

The software depends on [Node.js](http://nodejs.org) of at least version 16.
You can check your current version with:
```
  node -v
```
If you need to upgrade, a quick and easy way is:
```
  sudo npm install -g n
  sudo n stable
```
Now clone the MyCHIPs source code from the [github repository](github.com/gotchoices/mychips).
If the folder gets created as "MyCHIPs" (because you copied the github clone link) rather than 
"mychips", it may cause some problems on some platforms, so consider renaming it to "mychips."
```
  git clone https://github.com/gotchoices/mychips
  cd mychips
  npm install				#Install all dependencies
```
Now that the software is installed, you have 3 basic options to give it a try.
Note: the docker methods will require docker engine >= 20.10.10.
- [Docker Test Instance](use-docker.md):
  This is probably the easiest option and should work on Linux, Mac or Windows.
  It will help if you are already familiar with [Docker](http://docker.com).
  For Windows users, here are some known issues to be aware of:
  - Make sure docker [can mount your windows volumes](https://docs.docker.com/docker-for-windows/#shared-drives).
  - The "npm run docker" command will make use of the unixy "pwd" command (see inside package.json scripts).
    If you [configure npm to use bash](https://stackoverflow.com/questions/23243353/how-to-set-shell-for-npm-run-scripts-in-windows), this should work correctly.
    Otherwise you may have to execute the docker-compose command manually with the (MYCHIPS_ROOT and MYCHIPS_DIR environment variables set correctly).
    Some Windows users have better success running things in the [bash shell](https://gitforwindows.org/) that comes with Git.
  - Git on windows may automatically map UNIX text file LF terminators to CR-LF.
    This will alter certain scripts so the #!shebang command at the top doesn't work right.
    Hopefully, this has been addressed with a .gitattributes file in mychips/bin but if it pops up somewhere else, 
    [this](https://stackoverflow.com/questions/1019946/how-do-i-stop-git-from-adding-carriage-returns-when-cloneing-a-repo-onto-windows) explains how to configure your git when you clone the repo to avoid this.
  
- [Regular Linux Installation](use-native.md):
  You will need to install some dependencies and do a little configuration of the environment.
  But for a dedicated server, this is the way to go--at least for now.
  This should work fine on a Linux VM or a regular installation on physical hardware.

- [Docker Simulation](sim-docker.md):
  There are several simulation environments located in the test/sim directory.
  The latest version, based on docker, allows you to launch a number of MyCHIPs
  server instances in docker containers.  There is also an [agent model](sim-agent.md) module 
  that runs on behalf of simulated users to create a data set of random CHIP trades.

  To run the simulation, install Docker on your machine and then get into 
  the test/sim folder and follow the instructions [here](use-docker).

  The simulation environment was developed on MacOS but it should also be 
  possible (though not well tested) to run on a Linux host.
  Not much testing has been done on Windows but it may work with some effort.

<br>[Next - Docker Test Instance](use-docker.md)
<br>[Back to Index](README.md#contents)
