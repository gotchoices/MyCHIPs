drop table tmp;

create table tmp (
  val	varchar
);

drop view coldef;
create view coldef as select 
    pn.nspname		as sch
  , pc.relname		as tab
  , pat.attname		as col
  , pat.attnotnull	as nnl
  , pad.adsrc		as src
--  , pad.adbin		as bin
--  , pg_get_expr(pad.adbin,pc.oid)	as ssrc
  , 'new.' || quote_ident(pat.attname) || ' = coalesce(new.' || pat.attname || ',' || pad.adsrc || ')'	as defcmd

  from	pg_attrdef	pad
  join	pg_attribute	pat	on pat.attrelid = pad.adrelid and pat.attnum=pad.adnum
  join	pg_class	pc	on pc.oid = pat.attrelid
  join	pg_namespace	pn	on pn.oid = pc.relnamespace
  where pat.attnum > 0

--  where pc.relname='ent'
;
