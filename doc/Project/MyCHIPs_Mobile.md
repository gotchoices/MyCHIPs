# MyCHIPs Mobile Application
July 2020

## Project Background:
The current proof-of-concept release of MyCHIPs focuses on the testing and
evaluation of a set of backend [servers and processes](/doc/Scaling.odg).
But the success of the project will ultimately be dependent upon a moble 
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
The source tree includes an example of a [visual balance sheet](/doc/VisualBS.odg).
The goal with this graph is to show a user an intuitive indication of their net
wealth--a value that consists of the difference between their total assets and
their total liabilities.

In a CHIP accounting system, tallies (private credit agreements) are kept with
trading peers.  Each tally can contain a debit (asset) or a credit (liability)
balance at any given time.  One objective is to display in a single graph:
- Total assets
- Total liabilities
- Net value (assets - liabilities)
- Trading partners (whether by stock or foil)
- Individual balances with each trading partner

Additionally, the user interface will need the ability to do the following:
- Drill into an individual tally to see transaction history detaili
- Invite new peers to initiate a new tally agreement
- Respond to tally invitations (accept, modify, decline)
- Transmit value to direct peers and/or indirect parties (Linear lift)
- Invoice value from direct peers and/or indirect parties
- Respond to invoices (accept, modify, decline)
- Review/render tally trading contracts
- Generate/manage/protect connection keys
- Generate/manage/protect private trading keys
- Respond to alarms generated from the users host server
- Set/modify [trading parameters](/doc/Tallies)

Users whether consumers or sellers should be able to interact using the app
by generating QR codes on their screen and having the trading partner scan the
QR code in their app.  QR codes can also be shared using email or text 
messaging (out of MyCHIPs band communication).  This functionality is 
demonstrated in a rudientary way by the existing Wylib-based User Interface.

## Strategy:
- Choose a deployment framework:
  - Distributed web application (potential security issues)
  - Native applications (iPhone/Android)
  - NativeScript
  - Other?
- Create simple UI that starts with a graphical balance sheet visualizer
- Limited UI buttons/actions (Invite, Send, Request)
- Allow users to drill into deeper levels

## Outcomes:
- The mobile app is extremely easy for a new user to use
- No particular training is necessary
- All necessary prompting/help occurs in the course of use
- Mobile app communicates with the backend system via the existing API

## Technical Considerations:
The existing Wylib-based UI is for testing purposes only.  However it does
demonstrate some of the needed functionality.  Wylib includes a 
[module](http://github.com/gotchoices/wylib/src/wyseman.js) which provides
an encrypted/validated connection to the backend.  This includes an API that
can do CrUD (Create, Update, Delete) functions on the database.  It can also
invoke a variety of actions/reports which are invoked from the backend.

The mobile app should be a thin view-only layer that relies on the backend
for all control and model functionality (other than private key management).
