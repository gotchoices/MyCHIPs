## User Mobile Application

### General
As of this writing (Jan 2022) the mobile app is not yet functional.
There is a Flutter app originally written by the BYU Capstone team, but it is not yet
connected to the backend.

So the sections below represent design objectives and API definitions for what will
become the mobile application.


### Visual Balance Sheet
One important <i>eventual</i> goal of MyCHIPs to create a dependable, alternative medium of exchange.
Another critical goal is to build a diverse web of trusted links of interdependency 
throughout society in order to make the world a more peaceful and friendly place to live in.

In order to accomplish these goals, the end-user interface must be simple
enough for everyone to use and understand.
It will be an added bonus if the interface can imbue the user with deeper insights into:
  - The [true nature](http://gotchoices.org/mychips/value.html) of money/value
  - Sustainable and dependable savings strategies (Balance Sheet)
  - Healthy balance of productivity versus expenses (P&E)

Many people approach money management solely from the standpoint of meeting their monthly expenses (P&E).
They produce what they need to pay the bills.
If there is extra left over, it gets spent on luxuries.
If there is not enough, they may go without or try to obtain a raise or a better job.

This approach can leave people living close to the edge--sometimes only one paycheck away from financial disaster.

A more sustainable approach is to focus on the Balance Sheet, an indication of one's net worth, 
which is derived as the difference between one's assets and liabilities.  When people focus on 
increasing their net worth, the natural outcome is to produce more than they consume.

Like the P&E approach, this assures there is enough to cover expenses each month.  But it also 
encourages you to save a little each month.  That is the only way to get one's balance sheet to grow.

Since most people are not used to reading a balance sheet, it would be helpful
to have a very intuitive graphical way of displaying net worth--something that
could be understood with a glance and that would encourage people to behave in
a way that is in their best financial interest.

The "Visual Balance Sheet"
[prototyped here](https://rawcdn.githack.com/gotchoices/MyCHIPs/0fa1d6511d5f487d6928770e3cf3312bdc6d273e/test/visbs/index.html)
is intended to quantify several important aspects of one's balance sheet into 
a graphical object that is:
  - interesting to look at,
  - easy to understand,
  - fun to make changes that affect it in a positive way.

Quantities to model:
  - Total tally assets (stocks and debit-balance foils)
  - Total tally liabilities (foils and credit-balance stocks)
  - Number of tallies
  - Aggregate Magnitude (assets + liabilities)
  - Net Worth

Proposed Graph Dimensions:
  - Annular pie graph, relative size of slices
  - Hue of slices (asset/liability)
  - Shade of slices (different assets or liabilities)
  - Relative size and color of center core (net worth)

### User API
Processes communicate with the MyCHIPs server by exchanging JSON objects across sockets.
User applications do this through a user API.

There are several cases we will consider:
  - Application runs as a web app in a browser (existing demo SPA's)
  - Application is a web-app wrapped to feel more native (such as Ionic)
  - Application is fully native (such as Flutter)

In the first case (Single Page Application), the user directs his browser to
a trusted server where he can load the SPA over https.
The SPA then opens an encrypted websocket back to the same server to serve as a data connection.
This is all facilitated by the [Wyseman](https://github.com/gotchoices/wyseman) library.

The first time a user connects, he must have a connection ticket, which includes a one-time use token.
Upon presentation of the token, the database will allow a connection for that user.
Then the SPA will generate a permanent connection key and securely exchange keys with the server.
From then on, the user can connect by encryping a known object with the user's private key.

The particulars of this authentication scheme are not
separately documented, but can be examined in more detail in the
  - Wyseman [server source code](https://github.com/gotchoices/wyseman/blob/master/lib/wyseman.js),
  - Browser [client source code](https://github.com/gotchoices/wylib/blob/master/src/wyseman.js), and
  - Node.js [client source code](https://github.com/gotchoices/wyseman/blob/master/lib/client.js),

The Node.js client API module could be incorporated into a web application, such as in the Ionic framework.
A Dart API module is under development to facilitate a flutter implementation.

### Sample Command-line Client
There is a JS utility [here](https://github.com/gotchoices/MyCHIPs/blob/master/test/sample/entcli)
meant to demonstrate how to connect a client to the backend.

As mentioned, MyCHIPs uses [Wyseman](https://github.com/gotchoices/wyseman)
to form its API to the backend.  The [Wylib](https://github.com/gotchoices/wylib)
library has a compatible [module](https://github.com/gotchoices/wylib/src/wyseman.js) that
allows a client, running in a browser, to connect to the backend and send 
[CRUD](https://en.wikipedia.org/wiki/Create,_read,_update_and_delete) commands to the database.

The sample command line program demonstrates how to do this without a browser in node.js.
It makes use of a [client module](https://github.com/gotchoices/wylib/lib/client.js),
provided by Wyseman, that is similar to the browser-side code in Wylib and performs a comparable
function, allowing a user to authenticate and connect.

To test the sample CLI, get the MyCHIPs server running as explained [elsewhere](doc/Develop.md).
Generate a connection ticket:
```
  npm run adminticket
```

Then try running the client.  Note that for a docker-based server, the spa certificate will
be somewhere else (probably test/local/docker/pki).  Specifying it to the CLI is comparable with
installing it in your browser (or OS) for browser-based clients.
```
  cd test/sample
  ./entcli -a mychips0 -c ../pki/local/spa-ca.crt -t ../test/local/admin.json -u admin
```
The program will provide logging (typically in /var/tmp/wyatt/combined.log) if you have the
environment variable NODE_DEBUG set to "debug" or "trace".  The backend should be logging as
usual (in /var/tmp/mychips/combined.log) assuming its environment has NODE_DEBUG set.

The sample CLI will attempt to connect as the user you specify (admin).  If it succeeds, you
should get a "> " prompt.  You can type "list" to query the standard user table/view in the database.
There isn't much implemented other than "list" and "exit" as running commands is not really the point.
It is meant to demonstrate authenticating and connecting.

Once you have connected using a one-time connection token, the program will create a
permanent connection key and will store it in its "vault" ($USER/.mychips_keys).
Then you can connect more simply with:
```
  entcli -a mychips0 -c ../pki/local/spa-ca.crt
```
The key vault file is meant to be compatible with what is created/used in the browser-based sample GUI.
So you should be able to import that same file into the browser GUI and connect successfully.

### User API General Structure
User application developers should be aware of how to communicate with the backend:
- The software [model](https://en.wikipedia.org/wiki/Model%E2%80%93view%E2%80%93controller) is atomically contained in the PostgreSQL database.
- As it relates to the user API, the NodeJS server does the following:
  - Serves up a Single Page Application (not applicable to a native implementation)
  - Handles authentication of the user (using keys stored in the DB user record)
  - Connects the user to the DB <b>as the specific user ID</b> with its associated privileges
  - Receives JSON encoded commands from the user app, which can be
    - Abstracted SQL CRUD command
    - Abstracted SQL stored procedure all
    - A call to JS code (an "action) living in the NodeJS server
  - CRUD and stored procedures are simply translated to SQL, executed under the user's permissions, and the results returned to the app, tagged by the same transaction ID that generated the call.
  - Actions get executed by an assigned control layer (NodeJS) procedure, which will likely be interacting with the DB (and using admin permissions).
  - Actions can return results in a variety of formats:
    - Status only (similar to a stored procedure)
    - Text data
    - HTML display data
    - JPG/GIF/PDF/SVG image data
    - JSON data
    - A reference to an http URL which provides live, persistent and updatable results (dynamic report)

Status as of Jan 2022:
- The API framework is pretty well established and tested
- Enough of it for the admin SPA to function quite well.
- So far, any implementations of user-level interaction (such as simulators) have mostly been generated by issuing SQL commands directly to the DB (i.e. not going through the API).  This is just in order to concentrate on the server-to-server dynamics of the algorithm rather than user-server.
- There is a bare-bones user SPA running that connects to the server and can make a call to the API.
- The list of API calls that must be implemented can be gleaned from the green transitions shown on the four state diagrams [here](https://github.com/gotchoices/MyCHIPs/blob/master/doc/learn-protocol.md).
- Some of these can initially be done just with encoded SQL, but it will probably be helpful to memorialize most of them in stored procedures to simplify/harden use of the API.
- Data gathering aspects of the API will likely remain as encoded SQL selects.

### User API Objects
The User API is nearly a direct abstracton of the database connection itself.
During authentication, the user connects with a user ID maintained in the PostgreSQL database itself.

The Wyseman process receives JSON objects and translates them (mostly) to SQL
before forwarding those queries on to the database.
As responses come back from the database, they are relayed back to the user
application, along with an identifier unique to the query so they can be
correctly handled on the remote end.

The details of the communication objects can be determined by examining this
[server side code](https://github.com/gotchoices/wyseman/blob/master/lib/handler.js).

In brief, the object consists of at least these three properties:
- **id**: An unique identifier kept by the client so it can associate any response correctly with this query.
- **view**: The name of a database view, this action will be associated with.
  Although some actions may not strictly be bound to a view, everything is still associated with a view--particularly from the standpoint of the data dictionary.
- **action**: One of:
  - **lang**: A query of human readable titles, descriptions and tooltips associated with the named view.
  - **meta**: A query of database metadata such as field lengths, types, enumerated values, ranges and so forth associated with the named view.
  - **tuple**: The query is expected to return a single tuple.
  - **select**: The query is expected to return 0 or more tuples.
  - **update**: The query is intended to modify 0 or more tuples.
  - **insert**: The query contains information to insert a tuple.
  - **delete**: The query is intended to remove 0 or more tuples.

The received object may also include one or more of the following properties:
- **table**: A table name (or name of a stored procedure) should this need to differ from the "view" property mentioned above.
- **params**: An array of parameters to use, should the table actually indicate the name of a stored procedure.
- **fields**: An array of fields to include in a select query.
- **where**: An object describing what tuples to include in a select, update, or delete query.
  For details on this object's structure see "buildWhere()" function.
- **order**: An object describing how to sort tuples that are returned from a select query.
  For details on this object structure see "buildOrder()" function.

Once the query is complete, a result object will be returned to the caller, which includes these properties:
  - **id**: The original identifier.
  - **view**: The original view.
  - **action**: The original action.
  - **error**: An error object, if an error occurred in the transaction.
  - **data**: The data, if any returned by the transaction.
    This may differ greatly, depending on what type of transaction was requested.

In addition to the standard CRUD actions defined above, Wyseman allows the calling
application to include an extended action handler.
This is specifically handled in the
[dispatch manager](https://github.com/gotchoices/wyclif/blob/master/lib/dispatch.js),
part of the
[Wyclif](https://github.com/gotchoices/wyclif)
library.

MyCHIPs makes use of this in order to implement report handlers.
These are registered with Wyclif in the
[main program](https://github.com/gotchoices/MyCHIPs/blob/master/bin/mychips.js)
using the "Parser()" call currently around line 17.
And the report functions themselves are found in
[this](https://github.com/gotchoices/MyCHIPs/blob/master/lib/control1.js)
file and
[this](https://github.com/gotchoices/MyCHIPs/blob/master/lib/control2.js)
file.

Report handlers can return information in a variety of formats.
This can include html, svg, jpg and pdf, as well as JSON data that may be specific to
a particular UI widget.

For example, a user connection ticket is actually generated in the backend,
including the QR code.
The admin app needs only specify the report handler it wants to call and the
backend will serve up everything it needs in order to display the connection code.

### Key Security
A native web application has a notable security issue to deal with.
Specifically, the user application will be responsible for storing and managing the user's transaction signing key.
So you load an SPA from your CHIP Service Provider, and then connect to the same CSP to do your transactions.

A dishonest CSP could modify the SPA code such that it will disclose your key to him.
He would then be in possession of both your key and your data.

In the case of a wrapped or native application, you could get your app from one provider and then connect to a different service provider.
This gives more assurance that the code you are running won't betray you.

In high security applications, it may make sense for the signing key to not even reside in the user application.
It could instead reside in a separate key management device such as a USB or bluetooth dongle.

### Summary
Best advice for an application developer is:
- Get the server running;
- Enable logging as explained in the [instructions](README.md);.
- Try out the sample UI's (user and admin);
- Try out the [sample command-line UI](https://github.com/gotchoices/MyCHIPs/blob/master/test/sample/entcli);
- Experiment with reading and writing records;
- Experiment with calling reports;
- Insert additional logging commands where you need more information about what is going on;
- There are also logging commands you can uncomment in the SPI clients that will show up in the browser debug console;

<br>[Next - Simulations](sim.md)
<br>[Back to Index](README.md#contents)
