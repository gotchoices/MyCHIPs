## User Mobile Application

### General
As of this writing (Jul 2022) no mobile app is yet functional.
There is a Flutter app originally written by the BYU Capstone team, but it is not yet connected to the backend.
Update: as of Dec, 2022 an app based on React Native is under way [here](https://github.com/gotchoices/MyCHIPs/tree/dev/client/chark).

The sections below contain certain design objectives and API definitions for what 
will hopefully become the mobile application.
There is also a more detailed [project definition](Project/MyCHIPs_Mobile.md) that
was the original specification for Capstone but has since been improved and augmented.

### Visual Balance Sheet
The primary goal of MyCHIPs is to create a dependable, alternative medium of exchange.
A seconary goal is to encourage a diverse web of trusted links of interdependency 
throughout society in order to make the world a more peaceful and friendly place to live in.

In order to accomplish these goals, the end-user interface must be simple
enough for everyone to use and understand.
It will be an added bonus if the interface can imbue the user with deeper insights into:
  - The [true nature](http://gotchoices.org/mychips/value.html) of money/value
  - Sustainable and secure savings strategies (Balance Sheet)
  - Healthy balance of productivity versus expenses (P&L)

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
  - Application is fully native (such as Flutter or React Native)

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
  - Wyseman [client source code](https://github.com/gotchoices/wylib/blob/master/src/client_ws.js).

The JS client API module is written generally enough that it can work with a browser, node.js, React Native, etc.
A [Dart API](/client/flutter/lib/wyseman/wyseman_client.dart) module was partially written but has not been fully tested.

### Sample Command-line Client
There is a JS utility [here](https://github.com/gotchoices/MyCHIPs/blob/master/test/sample/entcli)
meant to demonstrate how to connect a client to the backend.

As mentioned, MyCHIPs uses [Wyseman](https://github.com/gotchoices/wyseman)
to form its API to the backend.  The [Wylib](https://github.com/gotchoices/wylib)
library has a compatible [module](https://github.com/gotchoices/wylib/blob/master/src/wyseman.js) that
allows a client, running in a browser, to connect to the backend and send 
[CRUD](https://en.wikipedia.org/wiki/Create,_read,_update_and_delete) commands to the database.

The sample command line program demonstrates how to do this without a browser in node.js.
It makes use of the [client module](https://github.com/gotchoices/wyseman/blob/master/lib/client_ws.js)
just as the Wylib SPA's do.

To test the sample CLI, get the MyCHIPs server running as explained [elsewhere](doc/Develop.md).
Generate a connection ticket:
```
  npm run adminticket
```
If your server is running in docker, you may need to run this inside that container.
You may also have to supply the hostname (-H) and/or other parameters compatible with your docker environment.
Specifically, the ticket needs to contain the correct host, port, user and token information.

Now try running the client.  Note that for a production docker-based server, the web certificate may
be somewhere else (like test/local/docker/pki).  Specifying it to the CLI is comparable with
installing it in your browser (or OS) for browser-based clients.
```
  cd test/sample
  ./entcli -a mychips0 -c ../../pki/local/web-ca.crt -t ../local/admin.json -u admin
```
The program will provide logging (something like /tmp/wyatt/combined.log) if you have the
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
  entcli -a mychips0 -c ../../pki/local/web-ca.crt
```
The key vault file is meant to be compatible with what is created/used in the browser-based sample GUI.
So you should be able to import that same file into the browser GUI and connect successfully.

### User API General Structure
User application developers should be aware of how to communicate with the backend:
- The software [model](https://en.wikipedia.org/wiki/Model%E2%80%93view%E2%80%93controller) is atomically contained in the PostgreSQL database.
- As it relates to the user API, the NodeJS server does the following:
  - Serves up a Single Page Application (not applicable to a native app implementation)
  - Handles authentication of the user (using keys stored in the DB user record)
  - Connects the user to the DB <b>as the specific user ID</b> with its associated privileges
  - Receives JSON encoded commands from the user app, which can be
    - Abstracted SQL CRUD commands
    - Abstracted SQL stored procedure call
    - A call to JS code (an "action" or "report") in the NodeJS server control layer
  - CRUD and stored procedures are simply translated to SQL, executed under the user's permissions, and the results returned to the app, tagged by the same transaction ID that generated the call.
  - Actions (or reports, if they return something) get executed by an assigned control layer (NodeJS) procedure, which will likely be interacting with the DB (and using admin permissions).
  - Reports can return results in a variety of formats:
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
- The list of API calls that must be implemented can typically be gleaned from the green transitions shown on the various state diagrams in [this section](https://github.com/gotchoices/MyCHIPs/blob/master/doc/learn-protocol.md).
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

The object may also include one or more of the following properties:
- **table**: A table name (or name of a stored procedure) should this need to differ from the "view" property mentioned above.
- **params**: An array of parameters to use, should the table actually indicate the name of a stored procedure.
- **fields**: An array of fields to include in a select query.
- **where**: An object describing what tuples to include in a select, update, or delete query.
  For details on this object's structure see "buildWhere()" function.
- **order**: An object describing how to sort tuples that are returned from a select query.
  For details on this object structure see "buildOrder()" function.

Once the query is complete, a result object will be returned to the caller, which includes these properties:
  - **id**: The original identifier from the caller.
  - **view**: The original view.
  - **action**: The original action.
  - **error**: An error object, if an error occurred in the transaction.
  - **data**: The data, if any returned by the transaction.
    This may differ greatly, depending on what type of transaction was requested.

In addition to the standard CRUD actions defined above, Wyseman allows the calling
application to include an extended action handler.
This is specifically handled in the
[dispatch manager](https://github.com/gotchoices/wyclif/blob/master/lib/dispatch.js),
part of the [Wyclif](https://github.com/gotchoices/wyclif) library.

MyCHIPs makes use of this in order to implement report handlers.
These are registered with Wyclif in the
[main program](https://github.com/gotchoices/MyCHIPs/blob/master/bin/mychips.js)
using the "Parser()" call currently around line 20.
And the report functions themselves are found in
[this folder](https://github.com/gotchoices/MyCHIPs/blob/master/lib/control).

Report handlers can return information in a variety of rendering formats.
This includes html but it can return general JSON data that may be meant to render in some
other widget or framework.

As one example, a user connection ticket is generated in the backend, including the QR code.
The admin app needs only specify the report handler it wants to call and the
backend will serve up everything it needs in order to display the connection code.

### Language Data
Wyseman also includes a facility for serving up a variety of dictionary data about database objects.
This can be expressed in any number of languages.

The intent is that a mobile app will draw all its language data from the backend.
So app developers should code apps using language tags and then populate the database with whatever language strings are necessary for the app to operate.

Language data are organized according to views, as in database views.
Each view (or table) will contain all manner of data explaining the title and detailed descriptions for 
the table itself, as well as all its columns.
In addition, each table/view can have any number of arbitrary messages associated with it.

An application wanting to access language data should execute something like this:
```
Wyseman.register(something_unique, view_name, (data, err) => {
  if (err) {<report errot>; return}
  local_reactive_variable = data
})
```
This will do an initial fetch of the metadata from the database associated with the requested view.
The wyseman module will also cache the data in memory for the duration of the object's existence.
If available, the data can also be cached in the devices local storage so that when an app launches
it will have all the language (and other) metadata from the previous session.

Subsequent register calls will still fetch fresh data from the database.
But in the mean time, display tags should still display correctly according to cached data.

Any time a user's language preference changes, you should call:
```
   Wyseman.newLanguage(lang)
```
This will fetch all new language data for all registered views.
If the app is built reactively, all language data in the app should change to display in the new language.

To get an idea of what language data is available, try this queries:
```
  select sch,tab,title,help,jsonb_pretty(to_jsonb(messages)) from wm.table_lang where tab = 'some_view'
```
Note that the database can also store any number of arbitrary JSON structures associated with a few.
These are called styles and can be queried as follows:
```
  select sch,tab,jsonb_pretty(styles) from wm.table_meta where tab = 'some_view'
```

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

### Initial Account Setup
Most mobile applications include some kind of facility for establishing an initial account.
For example, when you first launch the [Venmo app](http://venmo.com), it will step you through the process of becoming a Venmo customer.

An application intended to be part of the MyCHIPs open-source distribution is different in that it is not targeted for a single account service provider.
So rather than including sign-up screens, the app should assume that an account with a service provider already exists.
And it should attempt to connect using a connection ticket supplied by that service provider.

The expected sequence is as follows:
- The user will choose a service provider;
- The user navigates to a sign-up page on that provider's web site;
- The sign-up procedure gathers any necessary personal information to build the user's account;
- The web interface generates a one-time connection ticket using the ticket report in [this module](/lib/control1.js)
  or by generating a token using the mychips.ticket_login stored procedure in [this schema module](/schema/users.wms);
- The provider website then provides the user with one of the following:
  - A QR code (generated from the ticket report above) that can be scanned by the mobile app;
  - A [deep link](https://en.wikipedia.org/wiki/Mobile_deep_linking) which, when clicked, will automatically launch the mobile app and begin the connection/authentication procedure;

A mobile app should be capable of scanning several kinds of MyCHIPs QR codes.
If a connection ticket is found, the app should know to use it to attempt connection to the provider specified in the ticket.
If the app encounters a regular web URL, it should launch that URL in the user's preferred browser.
This way, if a provider provides QR with a link to it's sign-up page, the user will find his way there 
whether he is scanning the QR from his camera, scanning app, or MyCHIPs app.
If the provider provides a QR connection ticket, the user can use that too--but only if he is scanning from the MyCHIPs app.

### QR Connection Ticket Testing
For testing an app, you can create a QR code connection ticket from the [Admin UI](use-admin.md).
- Enable debugging (export NODE_DEBUG=debug) and watch the logging output of the server (tail -f /var/tmp/mychips/combined.log);
- Follow the procedure [here](use-test.md#testing-the-server) for creating some sample users;
- Then use the Users tab in the UI to preview (Launch Preview) the users;
- Double click on one of the users to open an editing pane for that user;
- Then find the Actions function in the associated menu;
- Under Actions, select User Ticket to display a QR code;
- The report window also gives the option for viewing/loading SVG, JSON and URL formats of the connection ticket.
- You can correlate the debugging output to what you see in the
  [generic dispatch launcher](http://github.com/gotchoices/wyclif/blob/master/lib/dispatch.js)
  and the [dedicated report module](/lib/control1.js).

Note that the displayed QR code is generated by the backend action/report system as described above.
Mobile apps are not expected to do this kind of work but should instead operate as thin views and rely on the backend and control layer for as much processing as possible.

The backend publishes what actions/reports are available to applications via its data dictionary.
If the app is written to make use of this feature, it will have to do very little to implement a new action/report that becomes available in the backend.
For example, query the data dictionary (using psql or similar SQL interface) as follows:
```
  select jsonb_pretty(styles) from wm.table_meta where sch = 'mychips' and tab = 'users_v';
```
This returns a JSON structure that includes an "action" property, an array of available actions/reports.
Calling applications can call an action handler, providing any arbitrary JSON data structure
and the handler can produce a customized report in any appropriate format.

In this case, the report generates a web page the app can present to the user.
Note that if you reload (right-click, reload) in the report window, the backend will not simply redisplay the QR code, but will in fact generate an entirely new ticket.

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

<br>[Next - Simulations](sim-docker.md)
<br>[Back to Index](README.md#contents)
