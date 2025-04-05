# MyCHIPs Backend Database Reference Guide

*Last updated: April 5, 2025*

## Overview

This document provides information about the MyCHIPS backend database, how to interact with it for debugging and testing, common queries, and key tables/views that are relevant to application development. The goal is to create a centralized resource for database-related information that was previously scattered across different issue files.

## Connection Methods

### Command Line (SSH)

For direct database queries from the command line:

```bash
ssh admin@mychips.net "psql mychips admin -c \"<SQL QUERY>\""
```

This allows you to run any SQL query against the database and see the results directly in your terminal.

### Application Communication (Wyseman API)

The MyCHIPs mobile application communicates with the backend using the Wyseman API over WebSockets:

- Connection is established through `src/connect.js`
- Message handling is managed by `src/wyseman.js`
- Communication happens via JSON packets sent over the socket
- Queries are executed against permissioned database views

## Key Database Objects

### Tables and Views

1. **Users and Certificates**
   - `mychips.users` - Core user information
   - `mychips.users_v` - User view with extended information
   - `mychips.users_v_me` - Personalized view of user information for the current connection

2. **Tallies**
   - `mychips.tallies` - Core tally data
   - `mychips.tallies_v` - Tally view with related certificate data
   - `mychips.tallies_v_me` - Personalized view of tallies for the current user
   
3. **Chits**
   - `mychips.chits` - Core transaction records
   - `mychips.chits_v` - Chit view with additional information
   - `mychips.chits_v_me` - Personalized view of chits for the current user

4. **Language and Text**
   - `wm.message_text` - App-specific text tags (view: 'chark')
   - `wm.table_text` - Descriptions of database tables
   - `wm.column_text` - Descriptions of table columns
   - `wm.value_text` - Descriptions of specific column values

### Common Fields

#### Tally Structure
- `json_core` - The exact data that was signed when creating a tally
- `hold_cert` - Certificate of the current user (holder)
- `hold_sig` - User's cryptographic signature of the tally
- `part_cert` - Partner's certificate
- `part_sig` - Partner's signature
- `tally_type` - Indicates whether the user holds the "foil" or "stock" side

#### Certificate Structure
- `chad` - Contains CUID, host, port, and agent information
- `name` - Contains name components (first, surname)
- `public` - Cryptographic public key for verification
- `connect` - Contact information (email, phone, etc.)
- `place` - Address information
- `identity` - Contains birth date and state information
- `date` - Certificate creation date

## Common Queries

### Querying Tallies

```sql
-- Get a specific tally with cryptographic data
SELECT json_core, hold_cert, hold_sig 
FROM mychips.tallies_v 
WHERE tally_ent = 'p1004' AND tally_seq = 46;

-- Get current user certificate
SELECT mychips.user_cert('p1004');

-- Update a tally's certificate with current user certificate
UPDATE mychips.tallies
SET hold_cert = mychips.user_cert('p1004')
WHERE tally_ent = 'p1004' AND tally_seq = 18;
```

### Querying Language Text

```sql
-- Query message tags for a specific view
SELECT mt_sch, mt_tab, code, language, title, help 
FROM wm.message_text 
WHERE language = 'eng' 
  AND mt_tab = 'chark'
  AND code IN ('tag1', 'tag2', 'tag3');

-- Query column descriptions for a specific table
SELECT ct_sch, ct_tab, ct_col, language, title 
FROM wm.column_text 
WHERE language = 'eng' 
  AND ct_tab = 'mychips.tallies_v_me';
```

## Special Database Functions

### Certificate Operations
- `mychips.user_cert(user_id)` - Returns the current certificate for a user
- `mychips.reassert_cert(tally_seq)` - Updates a tally's certificate with current key
- `mychips.reassert_sign(tally_seq)` - Updates a tally's signature

### User Operations
- `base.curr_eid()` - Gets the current user's entity ID
- `mychips.user_name(user_id)` - Returns formatted user name

## Data Structure Reference

### Tally Structure
A tally has two sides: a "foil" and a "stock", with each partner holding one side. The structure is:

```json
{
  "date": "ISO-8601 Date",
  "foil": {
    "cert": { /* Certificate Object */ },
    "terms": {}
  },
  "stock": {
    "cert": { /* Certificate Object */ },
    "terms": {}
  },
  "uuid": "Unique Identifier",
  "version": 1,
  "revision": 1
}
```

### Certificate Structure
Certificates contain user identity information and cryptographic keys:

```json
{
  "chad": {
    "cuid": "User ID",
    "host": "Server Host",
    "port": 12345,
    "agent": "Agent ID"
  },
  "date": "ISO-8601 Date",
  "name": {
    "first": "First Name",
    "surname": "Last Name"
  },
  "type": "p",
  "public": {
    "x": "Public Key X Component",
    "y": "Public Key Y Component",
    "crv": "Curve Type",
    "ext": true,
    "kty": "Key Type",
    "key_ops": ["verify"]
  },
  "connect": [
    {
      "media": "email|phone|cell|web",
      "address": "Contact Address"
    }
  ],
  "place": [
    {
      "type": "mail|phys",
      "address": "Street Address",
      "city": "City",
      "state": "State",
      "post": "Postal Code",
      "country": "Country"
    }
  ],
  "identity": {
    "birth": {
      "date": "ISO-8601 Date"
    },
    "state": {
      "country": "Country Code"
    }
  }
}
```

## Best Practices

1. **Sensitive Data**: Avoid querying sensitive user data like passwords/private keys
2. **Performance**: For large result sets, limit columns and add WHERE clauses
3. **Read-Only**: Prefer SELECT statements over modification statements when testing
4. **Testing**: Always test database modifications in a development environment before applying to production
5. **Troubleshooting**: Use JSON function operators to extract/examine nested fields
   ```sql
   -- Example: Extract a specific property from a JSON object
   SELECT tally_uuid, json_core->'foil'->'cert'->'name'->>'first' AS first_name
   FROM mychips.tallies_v
   ```

## Application Integration Considerations

1. **State Management**:
   - App relies on Redux for global state
   - UI components trigger requests to backend for data
   - Response updates Redux, UI components follow when visible
   - UI objects not visible still benefit from updated data
   - Backend can send unsolicited data which is also updated in Redux

2. **Error Handling**:
   - Implement consistent error feedback for the user
   - Add timeouts to prevent indefinite waiting for results
   - Consider a centralized error logging system

3. **Optimizations**:
   - Minimize unnecessary queries
   - Batch related queries when possible
   - Use appropriate indices for better performance

## Additional Resources

- [Wyseman Documentation](https://github.com/gotchoices/wyseman)
- [PostgreSQL Documentation](https://www.postgresql.org/docs/)
- [MyCHIPs Schema Reference](https://github.com/gotchoices/MyCHIPs/tree/master/schema)