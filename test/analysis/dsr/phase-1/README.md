# mychips-model

The model of MyCHIPs payments and lifts.

## Analysis
The main output document with the Lift protocol analysis and recommendations
based on the both TLA+ specification and general analysis of the protocol.  

## Diagrams

**diagrams** directory contains sequence diagrams showing positive and negative
scenarios of MyCHIPs payments and lifts. Each diagram is presented by two files:
the diagram source code in [PlantUML](https://plantuml.com) format and the
diagram rendered into a PNG image.

[PlantUML](https://plantuml.com) is a tool allowing users to create UML diagrams
from a [plain text language](https://plantuml.com/en/guide). Simple PlantUML
viewer can be downloaded
[here](http://sourceforge.net/projects/plantuml/files/plantuml.jar/download).
See [PlantUML Download Page](https://plantuml.com/download) for more options.
There are PlantUML plugins for most modern IDEs (e.g. [for
Eclipse](https://github.com/hallvard/plantuml) or [for Visual Studio
Code](https://marketplace.visualstudio.com/items?itemName=jebbs.plantuml)) which
allow editing diagrams in PlantUML format as well as exporting them to various
graphic formats. There is also a [lightweight online
editor](http://plantuml.com/plantuml) (allows export to PNG, SVG and ASCII Art
formats).

The behavior shown on all the diagrams except
**lift-cancel-final-commit-option** has been defined by **Lifts** specification
(see below).

## Specification

**spec** directory contains the TLA+ specification **Lifts** which describes
MyCHIPs payments and lifts. It includes the example model **LiftsExample** which
can be run by TLC model checker.

To run TLC model checker on **LiftsExample** model from the command line
interface see [Quick Start](#quick-start).

The specification can also be opened in TLA+ Toolbox IDE. This IDE provides a
convenient way to write specifications, edit models and run TLC model checker on
them. See [Opening Specification in TLA+
Toolbox](#opening-specification-in-tla-toolbox) for details.

### Quick Start

To run TLC model checker on **LiftsExample** model from the command line
interface do the following steps:

1. Install JRE (or JDK) version 8, 9 or 10 (we recommend to use [Amazon Correto
   8
   OpenJDK](https://docs.aws.amazon.com/corretto/latest/corretto-8-ug/downloads-list.html)).
2. Download [TLA+ Tools version
   1.5.7](https://github.com/tlaplus/tlaplus/releases/download/v1.5.7/tla2tools.jar)
   (we recommend to use the version 1.5.7 since it looks more stable than the
   version 1.7.0 which was the latest one at the moment when this manual was
   being written).
3. Clone this repository to your PC.
4. In **spec** directory execute:

```sh
java -cp PATH/TO/tla2tools.jar tlc2.TLC -simulate -depth 1000 -cleanup -deadlock -userFile user.log -config LiftsExample.cfg LiftsExample.tla
```

where

- `PATH/TO/tla2tools.jar` is the pathname of **tla2tools.jar** (alternatively
  you can add the pathname of **tla2tools.jar** to **CLASSPATH** environment
  variable and there will be no need to pass `-cp PATH/TO/tla2tools.jar` option
  to `java` command anymore)

TLC model checker will report its progress to stdout and also log generated
behaviors (state chains) to **user.log** file. The model checker will generate
random behaviors infinitely (until you stop the process).

### Specification Details

TLA+ Lift specification has been created for the Chit payment and Lift protocols:
- Chit payment positive case (as in `chit.png` diagram)
- Lift protocol positive case (as in `lift_success.png`)
- Lift cancellation cases (as in `lift_cancel_option1.png`)
- Malicious case when one of the non-originator nodes change the Lift value
- All the messages can be delayed up to some bound
- Messages can be received in a different order

Typically a TLA+ specification consists of:

- a specification module and the modules it uses (if any),
- models based on the specification module.

The specification module defines the behavior of a system and the safety and
liveness properties which must be held by the system. The specification module
specifies the system in a generic way and defines a number of system parameters.
In the specification module they are referred to as constants.

A model complements the specification module. A model provides the constant
parameters with specific values. So each model represents a specific system. A
model also specifies holding of which safety and/or liveness properties must
actually be checked by TLC model checker. Any model is presented either by an
auxiliary module and a configuration file or by a configuration file only. The
usual reason for use of the auxiliary module is impossibility to set constant
parameter values of some types using TLC configuration syntax. If the auxiliary
module is used then it extends the specification module and adds auxiliary stuff
necessary for the configuration definition.

The input to TLC model checker consists of a TLA+ module and a configuration
file. The TLA+ module which is passed to TLC model checker is either the
specification module or the auxiliary module of the model in case the model
includes it.

**Lifts** specification consists of:

- the specification module **Lifts.tla**,
- the example model **LiftsExample** consisting of the auxiliary module
  **LiftsExample.tla** and the configuration file **LiftsExample.cfg**.

TLC model checker (or simply TLC) verifies holding of safety and liveness
properties specified in the model for different possible behaviors (state
chains) of the system. TLC can do this verification in 2 modes: model check and
simulation. In the model check mode TLC calculates the complete state space
(i.e. finds all the reachable states), evaluating all the possible behaviors. In
the simulation mode TLC generates random behaviors infinitely (until you stop
the process).

Calculation of the complete state space can be done in an appropriate time for
only simple specifications. For most non-trivial specifications calculation of
the complete state space requires a huge period of time. So for **Lifts**
specification the simulation mode is the reasonable choice.

### Running TLC on Model from Command Line Interface

Before TLC can be run on **LiftsExample** model the following preliminary steps
must be fulfilled:

1. Install JRE (or JDK) version 8, 9 or 10 (we recommend to use [Amazon Correto
   8
   OpenJDK](https://docs.aws.amazon.com/corretto/latest/corretto-8-ug/downloads-list.html)).
2. Download [TLA+ Tools version
   1.5.7](https://github.com/tlaplus/tlaplus/releases/download/v1.5.7/tla2tools.jar)
   (we recommend to use the version 1.5.7 since it looks more stable than the
   version 1.7.0 which was the latest one at the moment when this manual was
   being written).
3. Add **tla2tools.jar** to **CLASSPATH** environment variable.
4. Clone this repository to your PC.

To run TLC on **LiftsExample** model in the simulation mode execute the
following command in **spec** directory:

```sh
java -Xmx<MAX_JAVA_HEAP_SIZE>m tlc2.TLC -simulate -depth <MAX_STATE_DEPTH> -workers <NUM_OF_WORKER_THREADS> -fpmem <MAX_RAM_TO_USE> -cleanup -coverage <COVERAGE_REPORT_INTERVAL> -deadlock -userFile <USER_LOG_FILENAME> -config LiftsExample.cfg LiftsExample.tla
```

where

- `-Xmx<MAX_JAVA_HEAP_SIZE>m` - (optional) sets the maximal Java heap space in
  MB.
- `-simulate` - sets the simulation mode,
- `-depth <MAX_STATE_DEPTH>` - sets the maximal state depth for the simulation
  mode, i.e. maximal behavior length **(1000 is the least recommended value for
  the example model)**; *by default the maximal state depth is 100.*
- `-workers <NUM_OF_WORKER_THREADS>` - (optional) sets the number of worker
  threads (however, it looks like that TLC always uses only 1 thread in the
  simulation mode); *by default 1 worker thread is used.*
- `-fpmem <MAX_RAM_TO_USE>` - (optional) sets the maximal amount of RAM that TLC
  may use (if an integer value then the amount in MB; if a fraction between 0
  and 1 then the fraction of the system RAM size); *by default 0.25 of the
  system RAM is used.*
- `-cleanup` - cleans up the states directory which TLC creates during its
  execution (in the simulation mode these directories contains no files, so it
  does not make sense to leave these directories after TLC execution; **but
  please note that this option is incompatible with the model check mode** - it
  causes `FileNotFoundException` in such case).
- `-coverage <COVERAGE_REPORT_INTERVAL>` - (optional) causes TLC to print a
  coverage report to stdout every <COVERAGE_REPORT_INTERVAL> minutes,
- `-deadlock` - makes TLC **not** consider deadlock (a situation when no other
  further step except stuttering is possible) as an error (in **Lifts**
  specification a successful termination is accompanied by deadlock, so this
  option **must always be used when using Lifts specification**).
- `-userFile <USER_LOG_FILE_PATH>` - sets the path for the user output file (in
  **Lifts** specification the actions with state numbers are logged into the
  user output file, this information is helpful for analyzing error traces and
  for getting information about behaviors being generated by TLC).

### Opening Specification in TLA+ Toolbox

**Lifts** specification can also be opened in TLA+ Toolbox. TLA+ Toolbox is an
IDE providing a convenient way to write specifications, edit models and run the
model checker on them. **spec/Lifts.toolbox** directory contains files being
created by TLA+ Toolbox. It includes the file **Lifts___LiftsExample.launch**
which is **LiftsExample** model in TLA+ Toolbox format. When the model checker
is launched from TLA+ Toolbox, the latter automatically converts the model from
***.launch** file to TLC format and puts the generated files **MC.tla** and
**MC.cfg** into **_<MODEL_NAME>_** subdirectory of ***.toolbox** directory of
the project.

To open **Lifts** specification in TLA+ Toolbox IDE do the following steps:

1. Install JRE (or JDK) version 8, 9 or 10 (we recommend to use [Amazon Corretto
   8
   OpenJDK](https://docs.aws.amazon.com/corretto/latest/corretto-8-ug/downloads-list.html)).
2. Download [TLA+ Toolbox version
   1.5.7](https://github.com/tlaplus/tlaplus/releases/tag/v1.5.7) ZIP package
   for your platform (we recommend to use the version 1.5.7 since it looks more
   stable than the version 1.7.0 which was the latest one at the moment when
   this manual was being written).
3. Unpack the downloaded ZIP package to any location you prefer.
4. Clone this repository to your PC.
5. Run **toolbox** executable file from the unpacked directory with TLA+
   Toolbox.
6. In the opened TLA+ Toolbox IDE open the main menu item **File > Open Spec >
   Add New Spec...**
7. In the opened dialog:
    1. In **Root-module file** field enter the full path to **spec/Lifts.tla**
       file from your working copy (click **Browse...** to select the file).
    2. **Specification name** will be automatically set to **Lifts** (the name
       of the module selected in the previous filed). Leave this value as is.
    3. Keep **Import existing models** checkbox marked.
    4. Click **Finish** button.

## Links

1. [TLA+ Home Page](http://lamport.azurewebsites.net/tla/tla.html)
2. [Specifying Systems](http://lamport.azurewebsites.net/tla/book.html) - the
   book about TLA+ from its creator Leslie Lamport
3. [TLA+ Toolbox on GitHub](https://github.com/tlaplus/tlaplus)
4. [TLA+ Toolbox Releases](https://github.com/tlaplus/tlaplus/releases) - TLA+
   Toolbox and TLA+ Tools can be downloaded from here
5. [TLA+ Toolbox User
   Guide](https://tla.msr-inria.inria.fr/tlatoolbox/doc/contents.html) (it can
   also be opened from locally installed TLA+ Toolbox by opening the main menu
   item **Help > Table of Contents**)
6. [Running TLA+ Tools
   Standalone](https://lamport.azurewebsites.net/tla/standalone-tools.html)
7. [TLC Model Checker Command-Line
   Options](http://lamport.azurewebsites.net/tla/tlc-options.html)
8. [PlantUML Home Page](https://plantuml.com)
