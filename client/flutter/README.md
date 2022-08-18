# MyCHIPs Mobile Application
This implementation was initially coded by a BYU Capstone team during the fall 2020 and
Winter 2021 semesters.  It is based on Flutter and was intended to achieve
basic functionality in conjunction with the existing server backend.

## Status
The capstone team built a number of the required screens, backed by MVVM-based boilerplate models.  Since then @n8allan built the beginnings of some manager infrastructure using reactive patterns, and has implemented Null safety across the code-base.

## Intended Features
- Connect and reconnect to the back-end
- Show or scan QR code to establish new tally relationships
- View and keep track of established tally relationships
- View and understand CHIP assets and liabilities
- See net value of CHIPs
- Pay or request payment from those you have tallies with
- Pay or request payment from an indirectly connected party

## Setup
- Run this in the app project directory to manually renerate the JSON serialization code, after changing any serialized structures:
  `flutter pub run build_runner build`
- Run this to start a watcher and have this run continuously:
  `flutter pub run build_runner watch`

## Build
- Follow the instructions to [install Flutter](https://flutter.dev/docs/get-started/install)
- In this (app) directory, do:
```
    flutter run
```
- Here is a good soup-to-nuts video tutorial on 
  [installation and user of flutter](https://www.youtube.com/watch?v=x0uinJvhNxI)

### TODO:
- Get token scanning UI working based on Test page (can paste or scan token)
- Add prompt for User if user isn't in the token (usually won't be)
- Redirect to token UI if connection needed, but lost or not established
- Build managers to pull various data for screens
- Connect UIs to various managers

## How ConnectionManager works
The `ConnectionManager` class is a singleton which manages the connection to the back-end.

### Reactive connections ###
The ConnectionManager exposes connectionStream, which is a stream of `Connection?`.  As is the pattern with reactive programming, this stream can be subscribed to to be notified whenever the connection changes or is broken (the connection will be null).

### Configuration ###
ConnectionManager is configured through it's `initialize` method, which should be given a stream of `HostConfig`.  The config is monitored, and if it changes, the connection is cleared.

### Establishing ###
To establish a connection, it must either have a key, which it attempts to load from storage at startup, or a ticket.  You can test whether it has a key using the hasKey member, e.g. `ConnectionManager().hasKey`.  If it doesn't provide a ticket (presumably through scanning a QR code or copy/paste), ensure that the ticket also has it's user member populated (the QR typically will not have this so the user will need to be prompted for this), then you can request the `connection` member to establish the connection, e.g. `await ConnectionManager().connection;`

### Other actions ###
To determine if a connection is established, use `ConnectionManager().connectionStream.hasValue`.  To clear the key, and prevent the device from automatically re-connecting, use `await ConnectionManager().clearKey()`.  To disconnect the current connection use `ConnectionManager().clearConnection();`
