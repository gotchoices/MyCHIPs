# MyCHIPs Mobile Application
This implementation was coded by a BYU Capstone team during the fall 2020 and
Winter 2021 semesters.  It is based on Flutter and was intended to achieve
basic functionality in conjunction with the existing server backend.

## Status
While the team did implement a number of the required screens, it was never
successfully connected to the backend.  So all data is simulated locally in 
the app.

## Intended Features
- Show or scan QR code to establish new tally relationships
- View and keep track of established tally relationships
- View and understand CHIP assets and liabilities
- See net value of CHIPs
- Pay or request payment from those you have tallies with
- Pay or request payment from an indirectly connected party

## Build
- Follow the instructions to [install Flutter](https://flutter.dev/docs/get-started/install)
- In this (app) directory, do:
```
    flutter run
```
- Here is a good soup-to-nuts video tutorial on 
  [installation and user of flutter](https://www.youtube.com/watch?v=x0uinJvhNxI)

### TODO:
- Finish porting the wyseman sebsocket client module to dart
- Back-port wyseman dart client code into wyseman distribution
- How to access wyseman.dart from wyseman npm distribution?
- Can/should wyseman also be distributed as a dart package (pub.dev)?
- Write DAOs to send/receive data and translate it for view
- Extend/refine backend actions/reports as necessary to serve UI
