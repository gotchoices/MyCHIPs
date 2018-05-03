-- Trying to trace a view column name back to a table column with a different name
-- Not sure if it is possible...

select
    nv.nspname		AS view_schema
  , v.relname		AS view_name
  , nt.nspname		AS table_schema
  , t.relname		AS table_name
  , ta.attname		AS column_name
  , ta.attnum		AS column_name
  , va.attname
--, dt.*

from	pg_namespace	nv
  join	pg_class	v	on v.relnamespace = nv.oid
  join	pg_depend	dv	on dv.refobjid = v.oid
  join	pg_depend	dt	on dt.objid = dv.objid and dt.refobjid <> dv.refobjid
  join	pg_class	t	on t.oid = dt.refobjid
  join	pg_namespace	nt	on nt.oid = t.relnamespace
  join  pg_attribute	ta	on ta.attrelid = t.oid and ta.attnum = dt.refobjsubid
--  join  pg_attribute	va	on va.attrelid = v.oid and va.attnum = 2

where	v.relkind	= 'v'
  and	dv.refclassid	= 'pg_catalog.pg_class'::regclass
  and	dv.classid	= 'pg_catalog.pg_rewrite'::regclass
  and	dv.deptype	= 'i'
  and	dt.classid	= 'pg_catalog.pg_rewrite'::regclass 
  and	dt.refclassid	= 'pg_catalog.pg_class'::regclass
  and	t.relkind IN ('r', 'v', 'f')
--  and	pg_has_role(t.relowner, 'USAGE')

and v.relname = 'address'
order by 6
;
