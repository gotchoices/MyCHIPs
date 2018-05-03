
select oid from pg_class where relname = 'address';	-- returns 110999
select oid from pg_class where relname = 'addr_v';	-- returns 110710

select attrelid::regclass, attname, attnum from pg_attribute where attrelid = 'json.address'::regclass and attnum > 0;
select attrelid::regclass, attname, attnum from pg_attribute where attrelid = 'base.addr_v'::regclass and attnum > 0;

select 	classid::regclass
      , objid::regclass
      , objsubid
      , refclassid::regclass
      , refobjid::regclass
      , refobjsubid
      , deptype
--from pg_depend where objid = 'json.address'::regclass;
from pg_depend where refobjid = 'json.address'::regclass;

-- select classid::regclass,objid::regclass,objsubid,refclassid::regclass,refobjid::regclass,refobjsubid,deptype from pg_depend where refobjid = 110710;
