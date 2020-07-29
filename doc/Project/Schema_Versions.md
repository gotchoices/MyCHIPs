# Wyseman Schema Control/Update Mechanism
July 2020

## Project Background:
The current proof-of-concept release of MyCHIPs relies on the
[Wyseman](http://github.com/gotchoices/wyseman) library for generating and
updating the PostgreSQL database schema.

One design objective for MyCHIPs is that production servers can be updated
to a later version without going offline.  The Wyseman design offers this
ability.  However, it has not yet been fully completed.

So far Wyseman has been used very successfully to maintain and update the
schema during development.  It stores SQL create/drop code in a separate 
area of the database itself.  Then as the developer makes changes to the 
[schema source code](/schema) wyseman can be run to compare the current
operating schema to the version contained in the source files.  Any database
objects that have been modified are dropped and re-created (or replaced) in
an atomic transaction which can occur while other transactions are occuring
in the database.

So far however, Wyseman has only been used to update and modify a "version 1"
schema.  The ultimate plan is to allow the developer to commit sequential
releases of the schema (2,3,4...) and Wyseman will save critical information
about each release in a control file documented 
[here](http://github.com/gotchoices/wyseman/doc/Versions).

## Objectives:
The goal of this project is to enhance the existing Wyseman tool so that
multiple schema versions can be published.  And any user of the MyCHIPs (or
other Wyseman-based software) can update its existing operating version to
the most current version (even if they are several versions behind).

## Strategy:
- Analyze/understand existing Wyseman code
- Analyze/understand suggested direction in "Versions" file
- Design/architect version control file format (preferably JSON-based)
- Modify Wyseman to include support functions
- Test/validate system

## Outcomes:
- MyCHIPs can commit regular schema release versions
- End users can download new versions at any time
- The new software will detect the current schema version
- The software will allow to update the schema version in real time
- Updates are atomic (will succeed or fail in their entirety)

## Technical Considerations:
The Wyseman command line utility is written in Ruby.

Wyseman schema definition files are written primarily in TCL data structures
which encapsulate SQL (and occasionally JSON).
