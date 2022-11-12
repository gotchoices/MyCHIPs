
## Schema Modifications

You can make changes to the schema files in this folder.  Schema changes can 
then be deployed to your current database by executing:
```
  make objects			#or: wyseman objects
```

Similarly, changes to text objects such as the names of tables, columns, etc 
can be rolled out with:
```
  make text
```

UI definitions can be deployed with:
```
  make defs
```

Data initializations can be made using:
```
  make defs
```

All of those can be done at once with:
```
  make all
```

Finally, you can update the schema distribution file (lib/schema.json) using:
```
  make schema
```

That file will be used to build a blank database when the mychips server is
launched for the first time.  It will also be consulted in case a schema 
needs to be updated to a current version.

Be careful when developing if you are deploying to multiple databases.  For example,
you might have a version of the database on a VM and some others in simulation docker
containers.  A db instance might be behind what is in the schema files at any given
moment.  If you need to update the database, run the "make all" command.

If the database is not at the usual default location, you may have to do something
like:
```
  wyseman --host=somehost --port=someport objects text defs
```
In some cases, your docker container db may seem difficult to reach from your
development machine.  For example, developing in a Linux VM under a Mac host, 
simulation containers running inside docker under the same Mac host.  The docker
container has exposed its port 5432 to the host, but that is not accessible to the
linux VM running under the host.

In such a case, it may be helpful to use an SSH tunnel to reach the postgres instance.
On the Linux VM:
```
  ssh user@host -L 5433:localhost:5432
```
Then you can reach postgres inside the VM on localhost, port 5433.

## Schema Versions
The database schema is published in distinct release versions by the wyseman schema manager.
The design description for how this works is found in: wyseman/doc/Versions.md.

Whatever release version is shown in Wyseman.hist is the one you are currently
working on (draft version of the next official release).  For example, if we 
are still working on release 1, we will se "release: 1" in Wyseman.hist but
there will be no commit dates in the "releases" array.

Similarly, looking at lib/schema.json, the release will be 1, but the publish
property will be 0 (false).

You can also see what release your current database instance is with his SQL query:
```
  select * from wm.releases
```

After working on schema changes, it will eventually be time to publish those changes.
You can do this by executing:
```
  make commit			#or: wyseman -C
```

This will assign a release date to the current working release and make it official.
Any changes to the schema you make after that are meant to apply to version 2.
This should also be reflected in the wm.releases table as there will now be a release
date for version 1 and version 2 will be the new working version.

During the development phases of MyCHIPs, versioning will likely not be actively used.
This means if you pull a later version from the repository, there are no good ways to
know if your schema is current.

Best bet if you're not sure is:
- Backup anything important in your database (hopefully there is nothing)
- Drop your database
- Restart mychips server so it will build schema from scratch
- Re-create any data conditions you need for testing

Hopefully when the system is more stable, officially versioned schemas will be
maintained and so the server will be able to update the schema on the fly as later
versions are encountered.
