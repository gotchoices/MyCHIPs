# MyCHIPs Mobile Application
July 2020

## Project Background:
The current proof-of-concept release of MyCHIPs focuses on the testing and
evaluation of a set of backend [servers and processes](/doc/Scaling.png).
But the success of the project will ultimately be dependent upon a mobile 
interface for the end user that is intuitive and easy to use.

There are existing applications we can learn from such as Paypal and Venmo.

Paypal has traditionally been a bit more difficult to use in a peer-to-peer
setting but does get used quite a bit in Ebay and other online commerce.

Venmo has emerged in Western markets as the choice for sending value from one
peer to another.  It suffers from certain privacy issues that bother some
people.  And it offers very little in the way of standardized monthly statements
which can be relied on for balancing financial statements and the like.

MyCHIPs has the additional challenge that it is dealing with a new (or very old)
kind of money that most modern people are not used to.  So it would benefit from
a graphical presentation that gives an instant and intuitive sense of how/where
value is stored and how it is transmitted.

## Objectives:
The source tree includes an example of a 
[visual balance sheet](/test/visbs/index.html).
The goal with this graph is to show a user an intuitive indication of their net
wealth--a value that consists of the difference between their total assets and
their total liabilities.

Note: the sample graph also includes the ability to visualize assets and
liabilities that are not held as CHIPs.
That is an advanced feature and need not be a part of the initial implementation.

In a CHIP accounting system, tallies (private credit agreements) are kept with
trading peers.  Each tally can contain a debit (asset) or a credit (liability)
balance at any given time.  One objective is to display in a single graph:
- Total assets
- Total liabilities
- Net value (assets - liabilities)
- Trading partners (whether by stock or foil)
- Individual balances with each trading partner

Additionally, the user interface will need the ability to do the following:
- Drill into an individual tally to see transaction history detail
- Invite new peers to initiate a new tally agreement
- Respond to tally invitations (accept, modify, decline)
- Transmit value to direct peers and/or indirect parties (Linear lift)
- Invoice value from direct peers and/or indirect parties
- Respond to invoices (accept, modify, decline)
- Review/render tally trading contracts
- Generate/manage/protect connection keys
- Generate/manage/protect private trading keys
- Respond to alarms generated from the users host server
- Set/modify [trading parameters](/doc/Tallies.md#trading-variables)

Users, whether consumers or sellers, should be able to interact using the app
by generating QR codes on their screen and having the trading partner scan the
QR code in their app.  QR codes can also be shared using email or text 
messaging (out-of-MyCHIPs-band communication).  This functionality is 
demonstrated in a rudientary way by the existing Wylib-based User Interface.

## Strategy:
- Choose a deployment framework:
  - Distributed web application (potential security issues)
  - Native applications (iPhone/Android)
  - NativeScript, React Native, Ionic, Flutter
  - Other?
- Create simple UI that starts with a graphical balance sheet visualizer
- Limited thin-view UI buttons/actions (Invite, Send, Request)
- Allow users to drill into deeper levels
- Connect thin-view to the backend server

## Outcomes:
- The mobile app is extremely easy for a new user to use
- No particular training is necessary
- All necessary prompting/help occurs in the course of use
- App communicates with the backend server via the existing websocket API

## Technical Considerations:
The existing Wylib-based UI is intended primarily for testing and development 
purposes.  However it does demonstrate some of the needed functionality.  Wylib 
includes a 
[module](http://github.com/gotchoices/wyseman/tree/master/lib/wyseman.js) that provides
an encrypted/validated connection to the backend.  This includes an API that
can do CrUD (Create, Update, Delete) functions on the database.  It can also
invoke a variety of actions/reports which are executed in the backend.

The mobile app should be a thin view-only layer that relies on the backend
for all control and model functionality (other than private key management and
storage).

## Tasks:
As of Spring 2021, a [rudimentary app skeleton](app/README.md) has been created 
in flutter.
The following are some task descriptions necessary to extend and mature it:

### Finish Wyseman Dart Module
A sample [JS test routine](/test/sample/entcli) as been provided to demonstrate
and test the basic function of the 
[JS Wyseman API module](http://github.com/gotchoices/wyseman/tree/master/lib/wyseman.js).

These two modules were provided by the app development team with the task of
porting wyseman.js to dart.  Much of that porting was done.  However, the team
got stuck around the issue of site certificates.

The websocket protocol is conducted over a secure SSL connection.  This means
the mobile device must recognize the server as trustworthy.
In most development environments, test instances of the server do not have
real SSL certificates, recognized by standard browsers and built-in SSL support
API's.  So (at least for development) clients will need to install a local 
certificate authority in order for the dart calls to allow connection over the 
websocket.  This is where the BYU team got stuck.

The partially ported wyseman dart code is [here](/app/lib/wyseman/wysemanClient.dart).
The task involves:
- Finish the port to dart, including full SSL/CA support
- Move the dart code into the Wyseman distribution
- Document how to get mobile devices to load a self-signed CA during development
- Include regression testing code in the Wyseman distribution
- How does a dart/flutter app properly access Wyseman (npm only or also pub.dev)?
  (Wyseman should properly support legacy tcl, ruby, javascript, and dart.)

### Write DAOs in Flutter App
The task involves:
- Existing view inputs call DAO's to request actions/reports from the backend
  (even if the backend has not fully implemented all such features)
- JSON data from the backend is properly tracked, parsed, presented to the user
- App extended and tested to correctly perform:
  - Connection key management; Users can:
    - receive a connection QR code from a service provider
    - make an initial websocket connection
    - safely store the permanent connection key
    - export the connection key to other devices as the user may direct
  - Signing key management; Users can:
    - be prompted to create a signing key just-in-time, as it is needed
    - safely store the signing key
    - safely retrieve the signing key using a passphrase
    - safely retrieve the signing key using biometrics available on the device
    - print a QR code of the signing key (to be stored in a safe deposit box)
  - Tally execution (control actions); Users can:
    - invite other users to a tally (generate QR code)
    - be invited to a tally (scan QR code)
    - view and select tally contracts (from a standard list on the backend)
    - negotiate and sign a tally (
    - select basic trading variables
    - view and update trading variables
  - Direct CHIT payments (control actions); Users can:
    - send signed CHIT to another user they share a tally with
    - request CHIT from another user they share a tally with
  - Indirect CHIT payments (control actions); Users can:
    - send value to arbitrary, specified user (initiate linear lift)
    - generate QR code to request value from arbitrary, specified payor

### Improve holdings Pie Chart
App home page shows intuitive pie chart indicating:
- Total assets CHIPs
- Total liability CHIPs
- Net value of CHIPs
- Value of other non-CHIP assets, quantified in CHIPs (advanced)

Users can initiate transactions with selected partners by touching them
on the pie chart, or attached nodes.
