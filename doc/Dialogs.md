## This is an outline of the dialogs that occur between processes:
Aug 2018 (Information likely to be outdated)

### Initialization/administration of site
- Upon first launch of the admin server:
  - If database not built, build it (need to finish wyseman command to do this from the app)
  - Execute any initialization scripts
  - Establish a site key, if one doesn't already exist

- The admin server should respond to the following commands (GUI/CLI):
  - Create a new user
  - Dump user data to json file
  - Load a new user from a json dump file
  - Edit user data, status
  - Issue user initial connection ticket
  - Create a new site key
  - Encrypt the site key (specify a new pass phrase)
  - Start peer server (requires the key pass phrase)
  - Stop peer server
  - Put a user (or the whole site) into lockdown mode
  - Edit site configuration defaults

### Initialization of keys between the user's mobile device and the user's site
- Initially, the service provider must set up a user account on its site
  This will include name, address, contact info, etc.
  But the provider should not know the user's private key information.
  This should eventually be kept on the mobile device.
  
  For initial prototyping, we may store the user's encrypted private key on the site server.
  It can be transmitted to the client, decrypted and used there to sign transactions.

- To get an initial connection, the provider admin creates a user ticket
  The ticket contains:
  - An Internet address, and port at which to connect to the site
  - A unique token, authorizing connection for this user without any key information
  - The site's public key
  Internally, the ticket has an expiration date, and the user's CDI.
  But the published ticket does not contain either of these items.
  The user must know his own CDI, and remember when the ticket expires.

- The mobile app reads the ticket information, storing the site's public key.
  It then connects on the specified address and port using SSL.
  The connection is configured to validate the server identity only.
  In other words, anyone with the ticket can connect.
  The client sends a structure (SSL encoded) containing:
    - The token
    - The user's CDI
    - The user's public key (create one if it doesn't already exist)
  If the site can decode this structure, and the token and CDI are valid, the server
    - Stores the user's public key,
    - Returns a success code: OK,
    - Closes the connection
  Otherwise, it returns nothing, refusing to read further information on the connection.
  Regardless, the token is invalidated and so can no longer be used.

### Normal connection between the user's mobile device and the user port server
- Connection is initiated by the mobile app
- Once connected, the app can query periodically for status updates, if desired.
- It might also open a secure socket on which to receive asynchronous alarms.
- Otherwise, if the site has an alarm for the user, this is sent via email/text
- Having received an alarm, the user can connect by launching the trusted app
  and query for status updates to determine the problem.

- The mobile app will connect at the private address and port
- It will send the CDI of the user connecting
- The SSL library will then validate the user using his public key, already known

- Once a private, secure connection has been achieved, 
  The server will enter a command interpretor mode:
  It will receive command structures,in json format, and
  return status structures, also in json format.

- The connection will remain open until one of the sides closes it.
  Normally the mobile app will do the closing.

### Initial connection between peer site servers
- User A will request a tally ticket for his account
  This authorizes a peer site to establish a connection, absent key information.
  The ticket will be disclosed to User B, via a reliable path.
  For example, User B will scan a bar code on User A's mobile device

- The ticket contains:
  - User A's CDI; the domain where to connect to do business with user A.
  - A unique token, authorizing connection without any key information
  - An expiration date
  - The site's public key

- Once in possession of the connection ticket,
  User B's site connects to User A's site.
  It sends a structure encoded with the site's public key, containing
    - The token
    - User B's CDI
    - The user B's site's public key
  If site A can decode this structure, and the token is still valid, it
    - Returns a success code: OK, and
    - Closes the connection
  Otherwise, it returns nothing, refusing to read further information on the port.
  Regardless, the ticket and its associated token are invalidated for further use.

### Normal connection between peer site servers
- Consider a connection initiated by the User A's site.
  In this case, we will call A's site the client.

- A's site, the client, connects to B's site and presents A's CDI
  B's site looks up A, and determines the correct site public key to expect
  The SSL library will then validate the connection using known keys

- Once a private, secure connection has been achieved, 
  The B server will enter a command interpretor mode:
  It will receive command structures,in json format, and
  return status structures, also in json format to the client.

- The connection will remain open until one of the sides closes it.
  Normally the A site, client, will do the closing.

- Either A's site or B's site can initiate a connection
  It is even possible to have both connections open at the same time.
  
