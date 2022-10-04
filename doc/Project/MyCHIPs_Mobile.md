# MyCHIPs Mobile Application
Updated Aug 2022

## Project Background
Early MyCHIPs development has focused primarily on the
[network of databases and process servers](/doc/uml/scaling.svg)
that form the matrix through which value is tracked and transmitted.
But the success of the project ultimately depends on a mobile 
interface for the end user that is intuitive and easy to use.

We can learn from existing applications such as Paypal and Venmo.

Paypal has traditionally been a bit more difficult to use between casual users
but it does get used extensively in online commerce.

Venmo has emerged in Western markets as the choice for sending value from one private individual to another.
It suffers from certain privacy issues that bother some people.
It seems to be a bit confused about whether it is a payment platform or a social medium.
And it offers very little in the way of standardized monthly statements which can be relied on for balancing financial statements and the like.

MyCHIPs has the additional challenge that it is utilizes two concepts most users are not used to:
- A new unit of measure.  This will feel a bit like using a foreign currency.
- The money is based on private credit rather than a central bank issue.
  This means money will exist in a number of different bins or wallets depending on which of the user's partners have issued it.

These differences need to be dealt with artfully so they do not create an undue obstacle for users.

## Current Status
As of Spring 2021, a [rudimentary application](/client/flutter/README.md) has been implemented
in flutter (by a BYU Capstone team).
It was designed according to an early version of this document.
But the team never succeeded in interfacing it to the backend so any data it
displays is purely simulated.

## The API
A [JavaScript API](http://github.com/gotchoices/wyseman/tree/master/lib/wyseman.js).
exists as part of the wyseman package.
There is also an example [JavaScript command line utility](/test/sample/entcli)
that makes use of the API module.

The Capstone team did attempt to port the JS API to Dart but did not successfully complete that work.
Their code is [here](/client/flutter/lib/wyseman/wyseman_client.dart).
Since that time, the Dart API has made some slow progress and can successfully connect
to the backend.
But it is not yet structured appropriately for integration into application.

The websocket protocol is conducted over a secure SSL connection.
This means the mobile device must recognize the server as trustworthy.
In most development environments, test instances of the server do not have
real SSL certificates, recognized by standard browsers and built-in SSL support API's.
So (at least for development) clients will need to install a local certificate 
authority in order for the dart calls to allow connection over the websocket.

Work yet to do on the API includes:
- Finish the port to dart, including full SSL/CA support
- Move the dart code into the Wyseman distribution
- Add support for distribution through normal Dart repository system (pub.dev?)
- Document how to get mobile devices to load a self-signed CA during development
- Include regression testing code for the API in the Wyseman distribution
- How does a dart/flutter app properly access Wyseman (npm only or also pub.dev)?
  (Wyseman should properly support legacy tcl, ruby, javascript, and dart.)

Additional information about the User Interface and API is available in
[this document](/doc/use-mobile.md).

## User Presentation
The app should present a simple set of buttons whose use and function is intuitive.
These include:
- Scan (QR code)  
  This allows the user to react to several kinds of actions from other users:
  - Scan a prospective partner tally ticket (invitation to tally)
  - Scan a vendor payment address, generate a request for invoice
  - Scan an offline check from a trading partner (future)
- Tally (Two partners shaking hands)  
  This begins the process of inviting another user to tally.
  It will immediately present a QR code, scannable by the other party, 
  which is an invitation to tally based on current default settings.
  It will also present buttons specific to this context:
  - Modify the credit amount offered to the other user.
  - Modify the selected tally contract.
  - Modify other tally credit parameters as per the system documentation.
- Pay (CHIP symbol with outbound arrow)  
  This button merely brings up a screen instructing the user how to actually pay:
  by selecting a partner from the balance sheet and then selecting Pay, or by
  scanning a payment address of a partner or remote peer user.
  [CHIP addresses](/doc/learn-users.md#chip-addresses)
  are long and cumbersome so there will be no way provided to type them in.
- Request (Question mark with inbound arrow)  
  Similarly, this button instructs the user to start by selecting a partner
  or scanning a peer CHIP address QR code.
- Settings (Gear Wheel)
  - Profile/certificate  
    Each user will need to establish his own certificate.
    This includes his name, address and other identifying information as
    explained [here](/doc/learn-tally.md#entity-certificates).
  - Language preference
  - Default tally parameters
    - Default tally contract
    - Default credit limit
  - Service provider
    - Hostname
    - Port
    - Connection key import/export
  - Signing key maintenance
    - Generate key (if it doesn't already exist)
    - [Securely](/doc/use-mobile.md#key-security) store the key
    - Validated recall (biometrics, passkey, etc)
    - Import/export key to other devices
  - Display preferences
    - Tabular or visual balance sheet
    - Preferred currency to provide automatic conversion to
    - Conversion ratio (or URL for automatic)
- History (ledger with time clock)  
  Show sortable/selectable history of all prior transactions.
  Selecting transactions will activate a menu to allow:
    - Pay this partner/peer again
    - Request payment from this partner/peer
- Help (Question mark)  
  This always displays in the same place and is responsive to whatever context the user is 
  currently in.  It will allow the user to get help screens without losing his place in
  the current process.

In addition to buttons, the main screen should display a balance sheet.
In an early iteration it will be acceptable to have only a tabular balance sheet.
By tabular, we mean a list of rows, each row pertaining to a tally.
The rows should display a partner name and a balance, and any other helpful information (like target) that may fit.

In the future, the user should be able to select between a visual and tabular sheet.

The source tree includes an example of a 
[visual balance sheet](https://rawcdn.githack.com/gotchoices/MyCHIPs/0fa1d6511d5f487d6928770e3cf3312bdc6d273e/test/visbs/index.html)
([source code](/test/visbs/index.html)).
The goal with this graph is to show the user an intuitive indication of their net
wealth--a value that consists of the difference between their total assets and
their total liabilities.

The sample graph also includes the ability to visualize assets and liabilities that are not held as CHIPs.
This is an advanced feature and need not be a part of the initial implementation.

Whether tabular or visual, the balance sheet should draw first attention to the user's
total net value of CHIP assets.
Then, the user should be able to discern how that total is derived from:
- Total assets (positive tallies); and
- Total liabilities (negative tallies)

Finally, the sheet should provide a list or a selection of individual tallies
with each different direct trading partner so the user can see whether each
tally has a positive or negative balance and what that balance is.

If the user touches a trading partner on the balance sheet, he should be offered
a context menu for:
- Sending payment
- Requesting payment
- Requesting invoice
- Viewing/setting trading parameters for the tally
- Viewing the tally contract
- View transaction history with that partner

Tallies that are not entirely executed (pending) should also be shown and be accessible
to interact with, review, submit, complete or reject.
Past closed tallies should be viewable upon request (or configuration) but not typically by default.

## Thin Client View
The mobile app should be only a view to the degree possible.
The API supports any arbitrary number of control-layer reports and generators to be
implemented and accessed.  These should be implemented for functions such as:
- Generating QR codes
- Generating tickets, invitations
- Rendering tallies and contracts
- Any other reports

Additionally, all human-language data shall be queried from the backend by an identifying token.
The database, control layer and API already supports this feature.
So once a language pack has been generated for and installed in the backend, the mobile app
should automatically be capable of operating in that language.

## Implementation
Unless there is a compelling reason to change the implementation language, it is
preferred to proceed using Flutter.

In the future it may be desirable to have several different mobile apps people can choose from.

## Outcomes
- The mobile app is easy for a new user to use
- No prior or external training is necessary to use the app
- All necessary prompting/help/learning occurs in the course of use
- App communicates with the backend server via the existing websocket API

## Getting Help on the Protocol
The protocol by which servers communicate with each other is described
[here](/doc/learn-protocol.md).
MyCHIPs includes an extensive set of regression tests that exercises the features
of this protocol.

In order to do so, they also simulate the actions of a user interface.
By examining these tests, it is possible to understand much about the
[CRUD](/doc/use-mobile.md#user-api-objects)
queries you will need to issue actions to, and process responses from the database.

## Page and Frame Designs
The following outlines a set of screens for a mobile app to accomplish the 
functionality described [above](#user-presentation).
- Frame: Profile Data
  - CHIP ID
  - surname, given names, company name
  - addresses
  - web, email, phone
  - Identity records
    - Tax ID number
    - Birth ID record
    - Photograph (ipfs hash?)

- Frame: Tally Data
  - Tally ID, data, notes
  - Partner certificate data and credit limit
  - Partner trading variable settings
  - Holder certificate data and credit limit
  - Holder trading variable settings
  - Current balance
  - Contract
  - Holder, signatures

- Page: Home
  - Display:
    - Balance sheet (visual or tabular)
    - Summary data: CHIP assets, liabilities, net total
    - Optional additional presentation in local currency (i.e. dollars)
  - Actions:
    - Touch: Select a tally -> Tally Edit
    - Button: Toggle visual/tabular balance sheet
    - Button: Add new tally (+) -> Tally Edit
    - Button: Scan QR code -> QR Scan
    - Button: Request Payment -> Invoice
    - Button: Settings -> Settings

- Page: QR Scan
  - Display:
    - Camera screen
    - Instructions?
  - Actions:
    - QR code may be one of the following types:
      - Connection ticket: create new account record, connect, -> Home
      - Tally ticket: -> Tally Edit
      - Payment address / Invoice: -> Pay
      - Chit: Queue to send to our provider when connected
    - Button: Home -> Home

- Page: Tally Edit
  - Display: Tally Data
  - Editable: Tally Frame (if not closed)
    - All applicable tally values (draft)
    - Trading variables (open/close)
  - Actions:
    - Button: Preview contract PDF
    - Button: Offer (draft)
    - Button: Accept (draft)
    - Button: Detail (open/close) -> Chits View
    - Button: Home -> Home

- Page: Chits View
  - List of chits including: date, id, type, amount, status
  - Actions:
    - Button: Home -> Home

- Page: Pay
  - Display:
    - Partner summary information (local tally)
    - Payment CHIP address (remote lift payment)
    - Optional conversion to local currency (dollars)
  - Editable:
    - Payment amount
  - Actions:
    - Pay: Initiate payment, -> Home
    - Home: Cancel, -> Home

- Page: Account
  - Display:
    - Provider address, port, connection key	(multiple providers/accounts?)
    - Signing key(s)				(multiple signing keys?)
  - Actions:
    - Import/export connection key
    - Import/export signing key
    - Generate signing key
    - Button: Home -> Home

- Page: Settings
  - Display:
    - Local currency
    - Notifications on/off
    - Preferred tally contract
    - Profile Data
  - Actions:
    - Button: Profile -> Profile
    - Button: Home -> Home

- Page: Profile
  - Editables:
    - Profile Data
  - Actions:
    - Button: Save: Save, -> Home
    - Button: Home -> Home

- Async: Tally offer, Invoice received, Payment received
  - Display: Notification
  - Actions:
    - Click: -> Tally Edit (on applicable tally)

## Project Phasing
After posting this project on Freelancer.com, it has become evident that it is
difficult to fully understand the scope of the project.  So this section has been
added to break the project down into smaller phases which can be taken on as
individual sub-projects.

This should also allow backend development and enhancements to keep pace with the
application development in a more orderly way.

In each phase, the code should be structured so as to reasonably accommodate
the later phases.  Each phase must also include unit tests for the implemented
features.

- Phase 1: Provider Connection / Authentication
  - Freshly launched app allows little other than to scan a QR connection ticket as first step
  - QR Scanner recognizes only one type so far: connection ticket
    - User scans connection ticket (QR generated by existing backend)
    - Prompt user for username (if not provided in ticket)
  - Generate and store local connection key securely
  - Perform key exchange/authentication with provider/server using Wyseman API
  - Show connection status with backend (at all times) on app screen
  - Fetch user profile and certificate data from backend
  - Demonstrate that UI buttons can send packets to backend
  - Demonstrate that backend packets can be received, interpreted and processed
  - User can select preferred language from what is available in backend
  - Language display data derived from backend in user's language of choice (using Wyseman schema objects)
  - Deep linking supported for connection ticket only (URL encoded connection ticket)
- Phase 2: Tally Initiation
  - App generates user signing key if not already present
  - Signing key securely stored
  - Tally Initiation button sends request packet to backend (the backend will generate a tally proffer QR for you)
  - Receive tally request according to Wyseman control layer protocol
  - Display tally proffer QR code on screen
  - Display functional share buttons to distribute QR on available media
    - Text, email, social media, print, etc.
  - Tally proffer can be shared as QR and/or deep link URL hyperlink
  - Maintain and display current list of tallies (only draft so far)
  - Implement tabular balance sheet only so far
- Phase 3: Tally Negotiation
  - QR scanner can also recognize and act on tally ticket
  - Deep linking now also supports reading a tally proffer
  - Upon receipt of either, take user to tally review screen
  - User can modify applicable tally parameters
  - Includes functional buttons to send appropriate packets to backend
    - Accept
    - Counter (if tally modified)
    - Reject
    - Review/share/print (backend report handler will generate PDF/html for you)
  - Tallies can be modified/countered any number of times
  - Accepted tally shows on tabular list of tallies (balance sheet)
  - Can launch to tally review screen when touching a tally in list
- Phase 4: Chit Handling
  - User can send unsolicited chit to partners on open tallies
  - User can request payment on open tallies
  - When app receives async chit (payment or request) user is notified
  - Server can push notifications to app
  - If app is not running, phone can receive notification
  - User can launch app from notification
  - Tally review screen has pay/request option
  - Chits can be transmitted as a QR and/or deep link URL
- Phase 5: Settings/Configuration
  - User can adjust common settings
    - Notifications
    - Profile, certificate information
    - Preferred tally contract
    - Preferred local currency
  - Connection key and signing key stored securely, extracted/validated using
    - Passphrase, and/or
    - Device-supported biometrics
- Phase 6: Visual Balance Sheet
  - Implement bubble chart balance sheet
  - User can select tabular or visual
  - Touching partners on the graph launches to tally review screen
- Phase 7: Deep Linking
  - User can receive media (text, email, etc) with hyperlink
  - Touching link in any media will launch MyCHIPs app to applicable page
  - User can receive links for:
    - Connection ticket (already done above)
    - Tally ticket (already done above)
    - Invoice
    - Check
- Phase 8: Enhancements
  - User profile can include photo
  - Photos referenced by ipfs, stored on provider server as ipfs
  - Use ipfs also for tally contracts

Other future phases likely to follow.
