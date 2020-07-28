# Network Visualizer
July 2020

## Project Background:
The current proof-of-concept release of MyCHIPs currently relies on the
[Wylib](http://github.com/gotchoices/wylib) library for its administrative
User Interface.

In addition to viewing/editing users and contract documents, this UI includes a 
network visualizer for observing local users and their remote connections in a 
graphical way.  See, for example page 4 of this [LibreOffice document](doc/Lifts.odg) 
or launch the simulation as explained [here.](test/sim/README.simdock).

The existing code, implemented in VueJS is part of Wylib, is mostly in the files:
[svgraph](http://github.com/gotchoices/wylib/src/svgraph.vue) and
[svgnode](http://github.com/gotchoices/wylib/src/svgnode.vue).

This code consists of a generic framework for displaying an abitrary bubble graph
which should be adaptable by the end-use application.  For example, in MyCHIPs, 
nodes are pictured as trading entities with attached tallies 
(stock assets or foil liabilities).  The particular drawing of these nodes is not
a part of the wylib library but is left to the MyCHIPs implementation.

The code is also used within the [wyclif](http://github.com/gotchoices/wyclif) 
package in the [wysegi](http://github.com/gotchoices/wyclif/src/wysegi) module
to display an ERD (Entity Releation Diagram) responsive to the current objects 
existing in an SQL database.

The code reads an existing data structure and then places nodes randomly in an 
SVG image.  It then does its best to connect the nodes according to the relational 
links found in the data set.

There is an included menu item "Arrange" which uses an attraction/repulsion model to 
try to spread out the nodes on the page in a reasonable way so it is more readable.
Nodes naturally repel each other, but connection links act like rubber bands to pull
nodes back together.  The goal is that nodes more closely related will be disposed
closer to each other on the screen.  There are also provisions for biasing placement
so (in the case of MyCHIPs) stock relationships will tend to move above and foil
relationships will tend to move below.

The current code has evolved to be a bit messy and complicated (particularly the 
code specific to MyCHIPs).  Also, it is iterative in nature.  Each time you press the
Arrange button, the graph takes a single iteration toward better order.  
In practice, one must hold the button for quite a while to get a readable graph.


## Objectives:
The goal of this project is to improve network visualization tool so it can more
efficiently display the graphical data that will be created using the 
[enhanced agent model simulator.](doc/projects/Agent_Model.md).

There are existing Javascript libraries that model graph dataabase content visually
including: [Cytoscape](https://js.cytoscape.org/).  It might be possible to use
such a library, or to learn from it.

One example is shown [here](https://cytoscape.org/cytoscape.js-cose-bilkent/).
This seems to quickly and efficiently create a layout for a given set of graph
data.  Admittedly, the MyCHIPs data set will be a lot more messy than what is shown
in the example.  This example does not appear to be deterministic, as it generates
a different result each time the button is pressed.

[This example](https://ivis-at-bilkent.github.io/cytoscape.js-fcose/demo.html)
reveals more of the parameters being used behnd the scenes to generate the graph.

[This example](https://cytoscape.org/cytoscape.js-cola/) appears to be a bit more
deterministic.  It also appears to be modeling forces in 3D in order to find more
pathways for the graph to "unfold" itself.  The current Wylib code only models
two dimensions so nodes more often get "stuck" and can't find a good path to
unfold.

Features should include:
- Apparently instant computation/placement of nodes/connections.
- If not instant, iteration should occur automatically, with the algorithm
  deciding on its own when it has converged on an acceptable solution.
- If parameters are tweaked, the graph should respond in real time (not requiring 
  additional (repaint) button pushes.
- The graph should find a "most readable" solution so a human observer can most
  readily see and understand the relational links between nodes.
- The graph should be able to handle datasets whether large or small.
- The end-use code should be able to customize the appearance and data content of 
  the nodes (at a minimum, this still works for the ERD case and the MyCHIPs case.
- The user can easily zoom in/out on the display and focus in on different areas
  of interest in the graph.
- A possible third use-case would be the display of a
  [Visual Balance Sheet](doc/VisualBS.odg) intended to be the home page of an
  eventual MyCHIPs mobile application.

## Strategy:
- Evaluate whether existing libraries can be used to generate the graph.
- Evaluate whether existing SVG libraries should be upgraded; or
  whether the graph should be a new, separate library function.
- Determine how code will best be integrated into Wylib/MyCHIPs environments.

## Outcomes:
- MyCHIPs Administrative console works with new visualization code
- No longer necessary to manually "arrange" nodes
- Module responds asynchronously to updates in the data set
- Graph converges (and terminates) automatically on a solution
- WyseGI ERD visualizer works with new codebase
- Possibly: MyCHIPs Visual Balance sheet works using this code

## Technical Considerations:
Wylib is currently implemented in VueJS.  For cleanest integration into the
existing environment, it seems wise to also make (keep) this as a VueJS
implementation.

