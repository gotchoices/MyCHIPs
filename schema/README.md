# MyCHIPs Schema System

This directory contains the schema definition files for the MyCHIPs database. The schema is defined using Wyseman, a schema management system that allows for version control, multi-language support, and automated database construction.

## Schema Modifications

You can make changes to the schema files in this folder. Schema changes can then be deployed to your current database by executing:
```
  make objects			#or: wyseman objects
```

Similarly, changes to text objects such as the names of tables, columns, etc. can be rolled out with:
```
  make text
```

UI definitions can be deployed with:
```
  make defs
```

Data initializations can be made using:
```
  make init
```

All of those can be done at once with:
```
  make all
```

Finally, you can update the schema distribution file (lib/schema.json) using:
```
  make schema
```

That file will be used to build a blank database when the mychips server is launched for the first time. It will also be consulted in case a schema needs to be updated to a current version.

Be careful when developing if you are deploying to multiple databases. For example, you might have a version of the database on a VM and some others in simulation docker containers. A db instance might be behind what is in the schema files at any given moment. If you need to update the database, run the "make all" command.

If the database is not at the usual default location, you may have to do something like:
```
  wyseman --host=somehost --port=someport objects text defs
```
In some cases, your docker container db may seem difficult to reach from your development machine. For example, developing in a Linux VM under a Mac host, simulation containers running inside docker under the same Mac host. The docker container has exposed its port 5432 to the host, but that is not accessible to the linux VM running under the host.

In such a case, it may be helpful to use an SSH tunnel to reach the postgres instance. On the Linux VM:
```
  ssh user@host -L 5433:localhost:5432
```
Then you can reach postgres inside the VM on localhost, port 5433.

## Schema Versions
The database schema is published in distinct release versions by the wyseman schema manager. The design description for how this works is found in: wyseman/doc/Versions.md.

Whatever release version is shown in Wyseman.hist is the one you are currently working on (draft version of the next official release). For example, if we are still working on release 1, we will see "release: 1" in Wyseman.hist but there will be no commit dates in the "releases" array.

Similarly, looking at lib/schema.json, the release will be 1, but the publish property will be 0 (false).

You can also see what release your current database instance is with this SQL query:
```
  select * from wm.releases
```

After working on schema changes, it will eventually be time to publish those changes. You can do this by executing:
```
  make commit			#or: wyseman -C
```

This will assign a release date to the current working release and make it official. Any changes to the schema you make after that are meant to apply to version 2. This should also be reflected in the wm.releases table as there will now be a release date for version 1 and version 2 will be the new working version.

During the development phases of MyCHIPs, versioning will likely not be actively used. This means if you pull a later version from the repository, there are no good ways to know if your schema is current.

Best bet if you're not sure is:
- Backup anything important in your database (hopefully there is nothing)
- Drop your database
- Restart mychips server so it will build schema from scratch
- Re-create any data conditions you need for testing

Hopefully when the system is more stable, officially versioned schemas will be maintained and so the server will be able to update the schema on the fly as later versions are encountered.

## Schema File Formats

The MyCHIPs schema system uses several file types to define different aspects of the database schema. All of these files are processed by Wyseman to generate the complete database schema.

### TCL Dynamic Lists
The schema files use Tcl (Tool Command Language) as a foundation, particularly its "list" data structures. Tcl lists can be nested and are used to organize the schema definitions. The config.tcl file defines global variables and namespaces that are used throughout the schema files.

### File Types

#### .wms (SQL Schema Files)
These files define the database schema structure in SQL, wrapped in Tcl lists. They contain:
- Table definitions with columns, constraints, and foreign keys
- View definitions
- Function and trigger definitions
- Schema grants and permissions

Key features:
- The `require` directive imports other TCL files
- `namespace eval` defines variables scoped to specific namespaces
- `module` sets the schema namespace
- `schema` creates database schemas
- `table`, `view`, `function`, and `trigger` keywords define database objects
- `def` defines reusable variable lists for column definitions
- `eval()` performs TCL evaluation within SQL strings
- `-grant` sections define object permissions

Example from users.wms:
```tcl
table mychips.users {base.ent mychips.agents} {
    user_ent    text    primary key references base.ent on update cascade on delete cascade
  , user_host   text
  , user_port   int     
  , user_stat   varchar not null default 'act' constraint "!mychips.users:UST" check (user_stat in ('act','lck','off'))
  ...
}
```

#### .wmt (Text Definition Files)
These files define language text for database objects, including:
- Table and column descriptions
- Value descriptions for enumerated types
- Error messages
- UI text for actions

The syntax uses the `tabtext` keyword followed by the schema object name, title, description, and column definitions.

Example from users.wmt:
```tcl
tabtext mychips.users {CHIP Users} {Entities who have CHIP accounts on this server} [concat {
  {user_ent    {User Entity}   {A link to the entities base table}}
  {user_host   {User Host Address} {The hostname or IP number where the users's mobile application connects}}
  ...
} $glob::stampt] -messages {
  {BRM {Birth Record Update}   {Birth record can only be written once by the user}}
  ...
}
```

#### .wmd (YAML Definition Files)
These are YAML files that define the UI display characteristics for database objects, including:
- Field display properties (size, position, type)
- Default values and validation
- Display columns
- Actions (buttons, forms)
- Subviews

Example from users.wmd:
```yaml
mychips.users:
  focus: ent_name
  fields:
  - [user_ent,    ent,  6,  [0,10],   {sort: 1, write: 0, hide: 1}]
  - [user_stat,   pdm,  10, [2,4],    {ini: act}]
  ...
```

#### .wmi (Initialization Files)
These are shell-executable files that initialize database tables with default values. They typically contain SQL INSERT statements. They're just shell scripts that output SQL.

Example from parm.wmi:
```sh
#!/bin/sh
cat <<EOF
insert into base.parm (module, parm, type, v_int, v_text, v_boolean, cmt) values 
  ('mychips', 'site_ent', 'text', null, 'r1', null, 'The ID number of the entity...')
 ,('agents', 'min_time', 'int', 5, null, null, 'Minimum number of minutes...')
...
EOF
```

### Macro Processor
The schema system includes a macro processor with `#define` statements for creating reusable code blocks. There are pre-defined macros for 'eval' and 'expr' which can be embedded in SQL inside a TCL string. The contents will be evaluated in the TCL environment and re-substituted back into the SQL.

### Build Process
The build process is controlled by Wyseman.conf and the Makefile:

- `Wyseman.conf` defines file patterns for each build target
- `make objects` compiles SQL schema (.wms)
- `make text` processes language definitions (.wmt)
- `make defs` processes UI definitions (.wmd)
- `make init` runs initialization scripts (.wmi)
- `make schema` produces a loadable schema file (lib/schema.json)
- `make sql` produces a readable SQL file for debugging

### Debugging Tips
- `make sql` will generate a complete SQL file that can be examined to confirm how the compilation has worked
- Using `eval(fld_list $variable)` in .wms files will expand a TCL list of field names
- The error messages from Wyseman can help identify syntax problems in the schema files

This schema system combines SQL, TCL, YAML, and shell scripting to create a flexible, version-controlled database definition system with built-in internationalization support and UI configuration.
