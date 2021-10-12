## MyCHIPs User Interface
Feb 2021

### Visual Balance Sheet
It is a critical goal of MyCHIPs to create a dependable, alternative medium of exchange.  
Another important goal is to build a diverse web of trusted links of interdependency 
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

There are three particular cases to consider here:
  - User Interface (including Admin) running as a web app in a browser
  - User Interface (including Admin) running as a native mobile app
  - Peer-to-peer server communications

In the first case (Single Page Application), the user directs his browser to
a trusted server where he can load the SPA over https.
The SPA then opens an encrypted websocket back to the same server to serve as a data connection.
This is all facilitated by the [Wyseman](https://github.com/gotchoices/wyseman) library.

The first time a user connects, he must have a connection ticket, which includes a one-time use token.  
Upon presentation of the token, the database will allow a connection for that user.  
Then the SPA will generate a permanent connection key and securely exchange keys with the server.
From then on, the user can connect by encryping a known object with the
user's private key.

The particulars of this authentication scheme are not
separately documented, but can be examined in more detail in the Wyseman
  - [server source code](https://github.com/gotchoices/wyseman/blob/master/lib/wyseman.js),
  - Browser [client source code](https://github.com/gotchoices/wylib/blob/master/src/wyseman.js), and
  - Node.js [client source code](https://github.com/gotchoices/wyseman/blob/master/lib/client.js),

There is also an [example client](https://github.com/gotchoices/MyCHIPs/blob/master/test/sample/entcli)
written in node.js that accepts a few simple commands and displays some raw results from the database on stdout.
This is not intended for production use, but demonstrates how to connect a UI to the backend.

For Peer-to-Peer communications, connections will eventually be secured using [Noise Protocol](http://www.noiseprotocol.org/).
Wyseman may eventually be extended to also allow connections via Noise Protocol but that is not currently implemented.
For now, user interfaces should use the websocket connection pattern and protocol.

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


### Summary
Apologies in advance for the scarcity of documention on the API.
Hopefully as it develops, there can be more help to develop both the API and its documentation further.

Best advice for now is:
- Get the server running;
- Enable logging as explained in the [instructions](README.md);.
- Try out the sample UI's (user and admin);
- Try out the [sample command-line UI](https://github.com/gotchoices/MyCHIPs/blob/master/test/sample/entcli);
- Experiment with reading and writing records;
- Experiment with calling reports;
- Insert additional logging commands where you need more information about what is going on;
- There are also logging commands you can uncomment in the SPI clients that will show up in the browser debug console;

### Some Older Design Notes (from 2017)
In addition to managing connections with other peer servers, a MyCHIPs server 
must manage connections with its own set of users.

It would be ideal if users could connect to their server in an entirely
different way than other peers do.  For example, the identity (or at least the
address and port) of my server will become known to one's partners as soon as
tallies are established with them.  It seems less than ideal if they can then 
use that information as the first step to try to hack into the user's account.

It would be perfectly feasible to accept user connections only on a different
port and even a completely different IP number.  Ideally, this endpoint would
be known only to the user who uses it.
