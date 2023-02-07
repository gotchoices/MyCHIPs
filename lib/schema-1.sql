--Bootstrap:
create schema if not exists wm;grant usage on schema wm to public;

create table if not exists wm.releases (
    release	int		primary key default 1 check (release > 0)
  , committed	timestamptz(3)
  , sver_2	int		-- Dummy column: bootstrap schema version
);
insert into wm.releases (release) values (1) on conflict do nothing;

create or replace function wm.next() returns int security definer stable language sql as $$
  select coalesce(max(release), 1) from wm.releases;
$$; revoke all on function wm.next from public;

create table if not exists wm.objects (
    obj_typ	text		not null		-- table, view, function, etc.
  , obj_nam	text		not null		-- schema.name
  , obj_ver	int		not null default 0	-- incremented when the object changes from the last committed release
  , checkit	boolean		default true		-- check dependencies
  , build	boolean		default true		-- modified, needs rebuild
  , built	boolean		default false		-- instantiated in current database
  , module	text		not null		-- name of the schema group this object belongs to
  , deps	text[]		not null		-- List of dependencies, as user entered them
  , ndeps	text[]					-- List of normalized dependencies
  , grants	text[]		not null default '{}'	-- List of grants
  , col_data	text[]		not null default '{}'	-- Extra data about columns, for views
  , delta	text[]		not null default '{}'	-- array of migration commands
  , del_idx	int		not null default 0	-- pointer to next unapplied delta
  , crt_sql	text		not null		-- SQL to create the object
  , drp_sql	text		not null		-- SQL to drop the object
  , min_rel	int		default wm.next() references wm.releases check (min_rel <= max_rel) -- smallest release this object belongs to
  , max_rel	int		default wm.next() references wm.releases	-- largest release this object belongs to
  , crt_date	timestamp(0)	default current_timestamp	-- When record created
  , mod_date	timestamp(0)	default current_timestamp	-- When record last modified
  , primary key (obj_typ, obj_nam, obj_ver)
);

create or replace function wm.releases_tf() returns trigger language plpgsql as $$
  begin
    if TG_OP = 'DELETE' then	-- Can only delete the latest
      return case when old.release < wm.next() then null else old end;
    elsif TG_OP = 'UPDATE' then	-- Can only update the date
      return case when new.release != old.release then null else new end;
    end if;
  end;
$$;
drop trigger if exists releases_tr on wm.releases;
create trigger releases_tr before update or delete on wm.releases for each row execute procedure wm.releases_tf();

create or replace function wm.objects_tf_bd() returns trigger language plpgsql as $$
  declare
    retval record = old;
  begin
    if old.obj_ver <= 0 then			-- Draft entry
      return old;
    elsif old.max_rel < wm.next() then		-- Historical object
      raise 'Object %:% part of an earlier committed release', old.obj_typ, old.obj_nam;
    end if;
    if old.max_rel > old.min_rel then		-- Object belongs to more than one release
      update wm.objects set max_rel = max_rel - 1 where obj_typ = old.obj_typ and obj_nam = old.obj_nam and obj_ver = old.obj_ver;
      retval = null;
    end if;
    if old.built then				-- Delete the instantiated object and its dependencies
      perform wm.make(array[old.obj_typ || ':' || old.obj_nam], true, false);
    end if;
    return retval;
  end;
$$;
drop trigger if exists objects_tr_bd on wm.objects;
create trigger objects_tr_bd before delete on wm.objects for each row execute procedure wm.objects_tf_bd();

create or replace view wm.objects_v_dep as
  with recursive search_deps(object, obj_typ, obj_nam, depend, release, depth, path, cycle) as (
      select (o.obj_typ || ':' || o.obj_nam)::text as object, o.obj_typ, o.obj_nam, null::text, r.release,0, '{}'::text[], false
 	from	wm.objects	o
 	join	wm.releases	r on r.release between o.min_rel and o.max_rel
  	where o.ndeps = '{}'            		-- level 1 dependencies
    union
      select (o.obj_typ || ':' || o.obj_nam)::text as object, o.obj_typ, o.obj_nam, d, r.release,depth + 1, path || d, d = any(path)
 	from	wm.objects	o
 	join	wm.releases	r	on r.release between o.min_rel and o.max_rel
 	join	unnest(o.ndeps)	d	on true
        join    search_deps     dr	on dr.object = d and dr.release = r.release	-- iterate through dependencies
        where			not cycle
  ) select object,obj_typ as od_typ, obj_nam as od_nam, depend, release as od_release, depth, path, cycle, path || object as fpath from search_deps;

create or replace view wm.objects_v as
       select o.obj_typ || ':' || o.obj_nam as object, o.*, r.release
  from		wm.objects	o
  join		wm.releases	r	on r.release between o.min_rel and o.max_rel;
  
create or replace view wm.objects_v_next as
    select * from wm.objects_v where release = wm.next();
  
create or replace view wm.objects_v_max as
    select o.*
    from	wm.objects	o
    where	o.obj_ver = (select max(s.obj_ver) from wm.objects s where s.obj_typ = o.obj_typ and s.obj_nam = o.obj_nam);
  
create or replace view wm.objects_v_depth as
  select o.*, od.depth
  from		wm.objects_v	o
  join		(select od_typ, od_nam, od_release, max(depth) as depth from wm.objects_v_dep group by 1,2,3) od on od.od_typ = o.obj_typ and od.od_nam = o.obj_nam and od.od_release = o.release
  order by	depth;

create or replace function wm.last() returns int security definer stable language sql as $$
  select max(release) from wm.releases where not committed isnull;
$$; revoke all on function wm.last from public;

create or replace function wm.create_role(grp text, subs text[] default '{}') returns boolean language plpgsql as $$
  declare
    retval	boolean default false;
    sub		text;
  begin
    if not exists (select rolname from pg_roles where rolname = grp) then
      execute 'create role ' || grp;
      retval = true;
    end if;
    foreach sub in array subs loop
      execute 'grant ' || sub || ' to ' || grp;
    end loop;
    return retval;
  end;
$$; revoke all on function wm.create_role from public;

create or replace language pltclu;
create or replace function wm.workdir(uniq text default '') returns text stable language pltclu as $$
  set path {/var/tmp/wyseman}
  if {$1 != {}} {set path "$path/$1"}
  if {![file exists $path]} {file mkdir $path}
  return $path
$$; revoke all on function wm.workdir from public;

create or replace function wm.grant(
    otyp	text		-- Object type we're granting permissions to
  , onam	text		-- Object name we're granting permissions to
  , priv	text		-- A privilege name, defined for the application
  , level	int		-- Application defined level 1,2,3 etc
  , allow	text		-- select, insert, update, delete, etc
) returns boolean language plpgsql as $$
  declare
    pstr	text default array_to_string(array[otyp||':'||onam,priv,level::text,allow], ',');
    grlist	text[];
    blt		boolean;	-- from object record
  begin
    select grants, built into grlist, blt from wm.objects where obj_typ = otyp and obj_nam = onam and obj_ver = 0;
    if not FOUND then
      raise 'Can not find defined object:%:% to associate permissions with', otyp, onam;
    end if;
    if pstr = any(grlist) then
      if not blt then raise notice 'Grant: % multiply defined on object:%:%', pstr, otyp, onam; end if;
      return false;
    else
      update wm.objects set built = false, grants = grlist || pstr where obj_typ = otyp and obj_nam = onam and obj_ver = 0;
    end if;
    return true;
  end;
$$; revoke all on function wm.grant from public;

create or replace function wm.hist(rel int = null) returns json language plpgsql as $$
  begin
    if rel isnull then
      rel = wm.next();
      if rel = wm.last() then	-- Make sure there is s development release
        rel = rel + 1;
        insert into wm.releases (release) values (rel);
        update wm.objects set max_rel = rel where max_rel = rel-1;
      end if;
    end if;
    return to_json(s) from (
      select rel as release, null as module,
      (select json_agg(coalesce(to_json(r.committed::text), '0'::json)) as releases
        from (select * from wm.releases where release <= rel order by 1) r),
      (select to_json(coalesce(array_agg(o), '{}')) as prev from
        (select obj_typ,obj_nam,obj_ver,module,min_rel,max_rel,deps,grants,col_data,delta,crt_sql,drp_sql
          from wm.objects_v where max_rel < rel order by 1,2) o)
    ) as s;
  end;
$$; revoke all on function wm.hist from public;

create or replace function wm.check_drafts(orph boolean default false) returns boolean language plpgsql as $$
  declare
    drec	record;		-- draft object record
    prec	record;		-- previous latest record
    changes	boolean default false;
  begin
    if orph then -- Find any orphaned objects (only works if there is at least one valid object remaining in each module)
      for drec in select o.*
        from wm.objects o
        join (select distinct module from wm.objects where obj_ver = 0) as od on od.module = o.module
        where wm.next() between o.min_rel and o.max_rel
        and o.module != ''
        and not exists (select obj_nam from wm.objects where obj_typ = o.obj_typ and obj_nam = o.obj_nam and obj_ver = 0)
      loop
raise notice 'Orphan: %:%:%', drec.obj_typ, drec.obj_nam, drec.obj_ver;
        delete from wm.objects where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam and obj_ver = drec.obj_ver;
      end loop;
    end if;

    for drec in select * from wm.objects where obj_ver = 0 loop		-- For each newly parsed record
      select * into prec from wm.objects_v_max where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam and obj_ver > 0;	-- Get the latest non-draft record
      if not found then
raise notice 'Adding: %:%', drec.obj_typ, drec.obj_nam;
        update wm.objects set obj_ver = coalesce((select obj_ver from wm.objects_v_max where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam), 0) + 1,
          checkit = true, build = true, mod_date = current_timestamp where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam and obj_ver = 0;
        continue;
      end if;

      if (drec.crt_sql  is distinct from prec.crt_sql)	or	-- Has anything important changed?
         (drec.drp_sql  is distinct from prec.drp_sql)	or
         (drec.deps     is distinct from prec.deps)	or
         (drec.col_data is distinct from prec.col_data)	or
         (drec.grants   is distinct from prec.grants)	or
         (drec.module   is distinct from prec.module)	then
       
        if prec.min_rel >= wm.next() then		-- if prior record starts with the current working release, then update it with our new changes
raise notice 'Modify: %:%', drec.obj_typ, drec.obj_nam;
          update wm.objects set checkit = true, build = true, module = drec.module, deps = drec.deps, grants = drec.grants, col_data = drec.col_data, crt_sql = drec.crt_sql, drp_sql = drec.drp_sql, mod_date = current_timestamp where obj_typ = prec.obj_typ and obj_nam = prec.obj_nam and obj_ver = prec.obj_ver;
          delete from wm.objects where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam and obj_ver = 0;
        else						-- else, prior record belongs to earlier, committed releases, so create a new, modified record
raise notice 'Increm: %:%', drec.obj_typ, drec.obj_nam;
          update wm.objects set max_rel = wm.next()-1, checkit = false, build = false, built = false where obj_typ = prec.obj_typ and obj_nam = prec.obj_nam and obj_ver = prec.obj_ver;
          update wm.objects set obj_ver = prec.obj_ver + 1, checkit = true, build = true, built = prec.built, mod_date = current_timestamp where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam and obj_ver = drec.obj_ver;
        end if;
      else						-- No changes from prior record, so delete the draft record
        delete from wm.objects where obj_typ = drec.obj_typ and obj_nam = drec.obj_nam and obj_ver = 0;
      end if;
    end loop;
    return true;
  end;
$$; revoke all on function wm.check_drafts from public;
    
create or replace function wm.check_deps() returns boolean language plpgsql as $$
  declare
    orec	record;		-- Outer loop record
    trec	record;		-- Dependency record
    d		text;		-- Iterator
    darr	text[];		-- Accumulates cleaned up array
  begin
    for orec in select * from wm.objects_v where release = wm.next() and checkit loop
      darr = '{}';
      foreach d in array orec.deps loop
          select * into trec from wm.objects_v where object = d and release = orec.release;	-- Is this a full object name?
          if not FOUND then
            begin
              select * into strict trec from wm.objects_v where obj_nam = d and release = orec.release;	-- Do we only have the name, with no type?
            exception
              when NO_DATA_FOUND then
                raise exception 'Dependency:% r%, by object:%, not found', d, orec.release, orec.object;
              when TOO_MANY_ROWS then
                raise exception 'Dependency:% r%, by object:%, not unique', d, orec.release, orec.object;
            end;
            d = trec.object;				-- Use fully qualified object name
          end if;
          darr = darr || d;
      end loop;
      update wm.objects set ndeps = darr, checkit = false where obj_typ = orec.obj_typ and obj_nam = orec.obj_nam and obj_ver = orec.obj_ver;		-- Write out cleaned up array
    end loop;
    return true;
  end;
$$; revoke all on function wm.check_deps from public;

create or replace function wm.replace(obj text) 
  returns boolean language plpgsql as $$
  declare
    trec	record;
  begin

    select * into strict trec from wm.objects_v where object = obj and release = wm.next();
    execute regexp_replace(trec.crt_sql,'create ','create or replace ','ig');
raise notice 'Replace:% :%:', trec.depth, trec.object;
    update wm.objects set built = true where obj_typ = trec.obj_typ and obj_nam = trec.obj_nam and obj_ver = trec.obj_ver;
    return true;
  end;
$$; revoke all on function wm.replace from public;

create or replace function wm.make(
    objs text[]			-- array of objects to act on
  , drp boolean default true	-- drop objects in the specified branch
  , crt boolean default true	-- create objects in the specified branch
) returns int language plpgsql as $$
  declare
    s		text;			-- temporary string
    trec	record;			-- temp record
    irec	record;			-- info record
    objlist	text[] default '{}';	-- expanded list of objects we will work on
    collist	text;			-- list of columns to save/restore in table
    cnt		int;			-- how many records saved/restored
    garr	text[];			-- grant array
    glev	text;			-- grant group_level
    otype	text;			-- object type, coerced to table for views
    counter	int default 0;		-- how many objects we build
    sess_id	text default (select to_hex(trunc(extract (epoch from backend_start))::integer)||'.'||to_hex(pid) from pg_stat_activity where pid = pg_backend_pid());
  begin
    if objs is null then		-- Defaults to drop/create of all objects needing build
      select into objs coalesce(array_agg(object), '{}'::text[]) from wm.objects_v where release = wm.next() and build;
    end if;

    select into objlist array_agg(distinct object) from wm.objects_v_dep o	-- Include dependencies
      join (select unnest(objs) as obj) as d on d.obj = any(o.fpath);
    create temporary table _table_info (obj_nam text primary key, columns text, fname text, rows int);

    if drp then			-- Drop specified objects
      for trec in select * from wm.objects_v_depth where object = any(objlist) and built order by depth desc loop
raise notice 'Drop:% :%:%', trec.depth, trec.object, trec.obj_ver;

        if trec.obj_typ = 'table' then
          begin
            execute 'select count(*) from ' || trec.obj_nam || ';' into strict cnt;
            exception when undefined_table then
              raise notice 'Skipping non-existant: %:%', trec.obj_typ, trec.obj_nam;
              continue;
          end;
          if crt then perform wm.migrate(trec); end if;		-- Need to modify table?
        end if;
        if trec.obj_typ = 'table' and cnt > 0 then		-- Attempt to preserve existing table data
          collist = array_to_string(array(select column_name::text from information_schema.columns where table_schema || '.' || table_name = trec.obj_nam order by ordinal_position),',');
          s = wm.workdir(sess_id) || '/' || trec.obj_nam || '.dump';
          execute 'copy ' || trec.obj_nam || '(' || collist || ') to ''' || s || '''';
          get diagnostics cnt = ROW_COUNT;
          insert into _table_info (obj_nam,columns,fname,rows) values (trec.obj_nam, collist, s, cnt);
        end if;

        execute trec.drp_sql;
      end loop;
    end if;

    if crt then			-- Create specified objects
      for trec in select * from wm.objects_v_depth where object = any(objlist) and release = wm.next() order by depth loop
raise notice 'Create:% :%:%', trec.depth, trec.object, trec.obj_ver;
        execute trec.crt_sql;
        
        if trec.obj_typ = 'table' then		-- Attempt to restore data into the table
          select * into irec from _table_info i where i.obj_nam = trec.obj_nam;
          if FOUND then
            execute 'copy ' || trec.obj_nam || '(' || irec.columns || ') from ''' || irec.fname || '''';
            execute 'select count(*) from ' || trec.obj_nam || ';' into strict cnt;
            if cnt != irec.rows then
              raise exception 'Restored % records to table % when % had been saved', cnt, trec.obj_nam, irec.rows;
            end if;
          end if;
        end if;
        
        foreach s in array trec.grants loop	-- for each specified object, expand to dependent objects
          garr = string_to_array(s,',');
          glev = garr[2] || '_' || garr[3];
          if garr[2] = 'public' then
            glev = garr[2];
          else
            perform wm.create_role(glev);
          end if;
          otype = trec.obj_typ; if otype = 'view' then otype = 'table'; end if;
          execute 'grant ' || garr[4] || ' on ' || otype || ' ' || trec.obj_nam || ' to ' || glev || ';'; 
        end loop;
        update wm.objects set built = true, build = false, checkit = false, del_idx = coalesce(array_length(delta, 1),0)
          where obj_typ = trec.obj_typ and obj_nam = trec.obj_nam and obj_ver = trec.obj_ver;
        counter = counter + 1;
      end loop;
    end if;

    drop table _table_info;
    return counter;
  end;
$$; revoke all on function wm.make from public;

create or replace function wm.migrate(orec record, max_ver int = null)
  returns boolean language plpgsql as $$
  declare
    del_idx	int = orec.del_idx;
    cmd		text;
    sql		text;
    trec	record;
    i		int default 0;
  begin
    foreach cmd in array orec.delta loop		-- for each migration command
      if i >= del_idx then				-- not already processed
        if cmd ~* '^(drop|rename|add)\s' then
          sql = 'alter table ' || orec.obj_nam || ' ' || cmd || ';';
        elsif cmd ~* '^update\s' then
          sql = 'update ' || orec.obj_nam || ' set ' || cmd ';';
        else continue;
        end if;
raise notice '  Delta: %:%: %', orec.obj_nam, orec.obj_ver, cmd;
        execute sql;
      end if;
      i = i + 1;
    end loop;

    if max_ver isnull then				-- at top recursion level
      max_ver = (select obj_ver from wm.objects_v_max where obj_typ = orec.obj_typ and obj_nam = orec.obj_nam);
      for trec in select * from wm.objects where obj_ver > orec.obj_ver and obj_ver <= max_ver order by obj_ver loop
        perform wm.migrate(trec, max_ver);		-- migrate any later versions
      end loop;
    end if;
    if orec.obj_ver < max_ver then			-- only the newly made version will do this in make
      update wm.objects set del_idx = i, built = false where obj_typ = orec.obj_typ and obj_nam = orec.obj_nam and obj_ver = orec.obj_ver;
    end if;
    return true;
  end;
$$; revoke all on function wm.migrate from public;


--Schema:
create type audit_type as enum ('update','delete');
create schema base;
grant usage on schema base to public;
create function comma_dollar(float8) returns text immutable language sql as $$
    select to_char($1,'999,999,999.99');
$$;
create function comma_dollar(numeric) returns text immutable language sql as $$
    select to_char($1,'999,999,999.99');
$$;
create function date_quart(date) returns text language sql as $$
    select to_char($1,'YYYY-Q');
$$;
create function eqnocase(text,text) returns boolean language plpgsql immutable as $$
    begin return upper($1) = upper($2); end;
$$;
create function is_date(s text) returns boolean language plpgsql immutable as $$
    begin 
      perform s::date;
      return true;
    exception when others then
      return false;
    end;
$$;
create schema json;
create schema mychips;
select wm.create_role('mychips_1');
grant usage on schema mychips to mychips_1;
create function neqnocase(text,text) returns boolean language plpgsql immutable as $$
    begin return upper($1) != upper($2); end;
$$;
create function norm_bool(boolean) returns text immutable strict language sql as $$
    select case when $1 then 'yes' else 'no' end;
$$;
create function norm_date(date) returns text immutable language sql as $$
    select to_char($1,'YYYY-Mon-DD');
$$;
create function norm_date(timestamptz) returns text immutable language sql as $$
    select to_char($1,'YYYY-Mon-DD HH24:MI:SS');
$$;
create extension "plpython3u";
create type tally_side as enum ('stock','foil');
create extension "uuid-ossp";
create function wm.column_names(oid,int4[]) returns varchar[] as $$
    declare
        val	varchar[];
        rec	record;
    begin
        for rec in select * from pg_attribute where attrelid = $1 and attnum = any($2) loop
            if val isnull then
                val := array[rec.attname::varchar];
            else
                val := val || rec.attname::varchar;
            end if;
        end loop;
        return val;
    end;
  $$ language plpgsql stable;
create table wm.column_native (
cnt_sch		name
  , cnt_tab		name
  , cnt_col		name
  , nat_sch		name
  , nat_tab		name
  , nat_col		name
  , nat_exp		boolean not null default 'f'
  , pkey		boolean
  , primary key (cnt_sch, cnt_tab, cnt_col)	-- each column can have only zero or one table considered as its native source
);
create table wm.column_style (
cs_sch		name
  , cs_tab		name
  , cs_col		name
  , sw_name		varchar not null
  , sw_value		varchar not null
  , primary key (cs_sch, cs_tab, cs_col, sw_name)
);
create table wm.column_text (
ct_sch		name
  , ct_tab		name
  , ct_col		name
  , language		varchar not null
  , title		varchar
  , help		varchar
  , primary key (ct_sch, ct_tab, ct_col, language)
);
create function wm.commit() returns jsonb language plpgsql as $$
  declare
    nxt int = wm.next();
  begin
    update wm.releases set committed = current_timestamp where release = nxt;
    insert into wm.releases (release) values (nxt + 1);
    update wm.objects set max_rel = nxt + 1 where max_rel = nxt;
    nxt = nxt + 1;
    return wm.hist(nxt);
  end;
$$;
create view wm.fkey_data as select
      co.conname			as conname
    , tn.nspname			as kyt_sch
    , tc.relname			as kyt_tab
    , ta.attname			as kyt_col
    , co.conkey[s.a]			as kyt_field
    , fn.nspname			as kyf_sch
    , fc.relname			as kyf_tab
    , fa.attname			as kyf_col
    , co.confkey[s.a]			as kyf_field
    , s.a				as key
    , array_upper(co.conkey,1)		as keys
  from			pg_constraint	co 
    join		generate_series(1,10) s(a)	on true
    join		pg_attribute	ta on ta.attrelid = co.conrelid  and ta.attnum = co.conkey[s.a]
    join		pg_attribute	fa on fa.attrelid = co.confrelid and fa.attnum = co.confkey[s.a]
    join		pg_class	tc on tc.oid = co.conrelid
    join		pg_namespace	tn on tn.oid = tc.relnamespace
    left join		pg_class	fc on fc.oid = co.confrelid
    left join		pg_namespace	fn on fn.oid = fc.relnamespace
  where co.contype = 'f';
grant select on table wm.fkey_data to public;
create view wm.lang as select true;
create table wm.message_text (
mt_sch		name
  , mt_tab		name
  , code		varchar
  , language		varchar not null
  , title		varchar		-- brief title for error message
  , help		varchar		-- longer help description
  , primary key (mt_sch, mt_tab, code, language)
);
create view wm.role_members as select ro.rolname				as role
  , me.rolname					as member
  , (string_to_array(ro.rolname,'_'))[1]	as priv
  , (string_to_array(ro.rolname,'_'))[2]	as level
    from        	pg_auth_members am
    join        	pg_authid       ro on ro.oid = am.roleid
    join        	pg_authid       me on me.oid = am.member
    where not ro.rolname like 'pg_%';
create function wm.table_rest(obj text, tag text) returns int language plpgsql as $$
  declare
    count	int;
    file text = wm.workdir(current_database()) || '/' || obj || '-' || tag || '.save';
    collist	text = array_to_string(
      array(
        select column_name::text from information_schema.columns where table_schema || '.' || table_name = obj order by ordinal_position
    ),',');
  begin
    SET session_replication_role = replica;
    execute 'delete from ' || obj;
    execute 'copy ' || obj || '(' || collist || ') from ''' || file || '''';
    execute 'select count(*) from ' || obj || ';' into strict count;
    SET session_replication_role = DEFAULT;
    return count;
  end;
$$;
create function wm.table_save(obj text, tag text) returns int language plpgsql as $$
  declare
    count	int;
    file text = wm.workdir(current_database()) || '/' || obj || '-' || tag || '.save';
    collist	text = array_to_string(
      array(
        select column_name::text from information_schema.columns where table_schema || '.' || table_name = obj order by ordinal_position
    ),',');
  begin
    execute 'copy ' || obj || '(' || collist || ') to ''' || file || '''';
    get diagnostics count = ROW_COUNT;
    return count;
  end;
$$;
create table wm.table_style (
ts_sch		name
  , ts_tab		name
  , sw_name		varchar not null
  , sw_value		jsonb not null
  , inherit		boolean default true
  , primary key (ts_sch, ts_tab, sw_name)
);
create table wm.table_text (
tt_sch		name
  , tt_tab		name
  , language	varchar not null
  , title		varchar
  , help		varchar
  , primary key (tt_sch, tt_tab, language)
);
create table wm.value_text (
vt_sch		name
  , vt_tab		name
  , vt_col		name
  , value		varchar
  , language		varchar not null
  , title		varchar		-- Normal title
  , help		varchar		-- longer help description
  , primary key (vt_sch, vt_tab, vt_col, value, language)
);
create view wm.view_column_usage as select * from information_schema.view_column_usage;
grant select on table wm.view_column_usage to public;
create schema wylib;
grant usage on schema wylib to public;
create table base.country (
code	varchar(2)	primary key
  , com_name	text		not null unique
  , capital	text
  , cur_code	varchar(4)	not null
  , cur_name	text		not null 
  , dial_code	varchar(20)
  , iso_3	varchar(4)	not null unique
  , iana	varchar(6)
);
create table base.language (
code	varchar(3)	primary key
  , iso_3b	text		unique
  , eng_name	text		not null
  , fra_name	text		not null
  , iso_2	varchar(2)	unique
);
create function base.priv_role(uname name, priv text, lev int) returns boolean security definer language plpgsql stable as $$
    declare
      trec	record;
    begin
      if uname = current_database() then		-- Often true for DB owner
        return true;
      end if;
      for trec in 
        select role, member, priv, level from wm.role_members rm where member = uname and rm.priv = priv or rm.level is null order by rm.level desc loop
raise notice 'Checking % % % % %', uname, trec.role, trec.priv, trec.level, trec.member;
          if trec.rpriv = priv and trec.level >= lev then
              return true;
          elsif trec.level is null then
              if base.priv_role(trec.role, priv, lev) then return true; end if;
          end if;
        end loop;
        return false;
    end;
$$;
create operator =* (leftarg = text,rightarg = text,procedure = eqnocase, negator = !=*);
revoke all on schema public from public;
  grant all on schema public to admin;
create function mychips.b64v2ba(input text) returns bytea language sql immutable as $$
    select decode(
      translate(input, '_-','/+') || repeat(
        '=', mod(4 - mod(char_length(input)::numeric, 4.0)::int, 4)	-- Pad to modulo 4 length
      ), 'base64'
    )
$$;
create function mychips.ba2b64v(input bytea) returns text language sql immutable as $$
    select translate(encode(input, 'base64'), E'/+=\n', '_-');
$$;
create function mychips.chit_state(isdebit boolean, status text, request text) returns text immutable language sql as $$
    select
      case when isdebit then 'A.' else 'L.' end ||
      status ||
      case when request isnull then '' else '.' || request end;
$$;
create function mychips.contract_url(dom text, nam text, ver int, lan text, dig text) returns text immutable language sql as $$
    select dom || '/' || nam || '-' || ver::text || '-' || lan || case when dig is null then '' else '?' || dig end;
$$;
create function mychips.j2h(input jsonb) returns bytea language plpython3u immutable as $$
    import json
    import hashlib
    if isinstance(input, str):		#JSON gets passed into python as a string
      obj = json.loads(input)		#Parse JSON
    else:
      obj = input
    serial = json.dumps(obj, separators=(',',':'), sort_keys=True)	#Repeatable serialization
#    plpy.notice('j2h:', serial)
    hash = hashlib.sha256(serial.encode('utf-8'))
    return hash.digest()
$$;
create function mychips.j2s(inp jsonb) returns text language plpython3u immutable as $$
    import json
    if isinstance(inp,str):		#JSON gets passed into python as a string
      obj = json.loads(inp)
    else:
      obj = inp
#    plpy.notice('j2s:', obj)
    s = json.dumps(obj, separators=(',',':'), sort_keys=True)
    return s
$$;
create function mychips.lift_state(status text, request text) returns text stable language sql as $$
    select
      status ||
      case when request isnull then '' else '.' || request end;
$$;
create function mychips.route_sorter(status text, expired boolean) returns int stable language plpgsql as $$
    begin return case
      when status = 'good' and not expired	then	0
      when status = 'pend' and not expired	then	1
      when status = 'good' and expired		then	2
      when status isnull			then	3
      when status = 'pend' and expired		then	4
      else						5 end;
    end;
$$;
create function mychips.route_state(status text, expired boolean) returns text stable language plpgsql as $$
    begin return
      status ||
      case when status in ('pend','open') and expired then '.X' else '' end;
    end;
$$;
create function mychips.state_updater(recipe jsonb, tab text, fields text[], qflds text[] default null) returns text immutable language plpgsql as $$
    declare
      lrec	record;
    begin
      if qflds is null then
        qflds = '{"request = null", "mod_date = current_timestamp", "mod_by = session_user"}';
      end if;
      for lrec in select * from jsonb_each_text(recipe->'update') loop

        if lrec.key = any(fields) then		-- update only allowable fields
          qflds = qflds || (quote_ident(lrec.key) || ' = ' || quote_nullable(lrec.value));
        end if;
      end loop;
      return 'update ' || tab || ' set ' || array_to_string(qflds,', ') || ' where ';
    end;
$$;
create function mychips.tallies_tf_change() returns trigger language plpgsql security definer as $$
    begin
raise notice 'Admin tallies notify:%', TG_OP;
      perform pg_notify('mychips_admin', format('{"target":"tallies", "oper":"%s", "time":"%s"}', TG_OP, transaction_timestamp()::text));
      return null;
    end;
$$;
create function mychips.tally_state(status text, request text, hold_sig text, part_sig text) returns text immutable language plpgsql as $$
    begin return
      case when status = 'offer' then
             case when hold_sig isnull and not part_sig isnull then	'P.'
                  when part_sig isnull and not hold_sig isnull then	'H.'
                  else 'B.' end
           else '' end ||
      status ||
      case when request isnull then '' else '.' || request end;
    end;
$$;
create function mychips.users_tf_change() returns trigger language plpgsql security definer as $$
    begin

      perform pg_notify('mychips_admin', format('{"target":"users", "oper":"%s", "time":"%s"}', TG_OP, transaction_timestamp()::text));
      return null;
    end;
$$;
create function mychips.validate(dat text, sig text, pub text) returns boolean language plpython3u immutable as $$
#    plpy.notice('Validate:', dat, sig, pub)
    import rsa

    pubkey = rsa.PublicKey.load_pkcs1_openssl_pem(pub)
    signature = bytearray.fromhex(sig)
    verified = rsa.verify(dat, signature, pubkey)

    return verified
$$;
create operator !=* (leftarg = text,rightarg = text,procedure = neqnocase, negator = =*);
create view wm.column_ambig as select
    cu.view_schema	as sch
  , cu.view_name	as tab
  , cu.column_name	as col
  , cn.nat_exp		as spec
  , count(*)		as count
  , array_agg(cu.table_name::varchar order by cu.table_name desc)	as natives
    from		wm.view_column_usage		cu
    join		wm.column_native		cn on cn.cnt_sch = cu.view_schema and cn.cnt_tab = cu.view_name and cn.cnt_col = cu.column_name
    where		view_schema not in ('pg_catalog','information_schema')
    group by		1,2,3,4
    having		count(*) > 1;
create view wm.column_data as select
    n.nspname		as cdt_sch
  , c.relname		as cdt_tab
  , a.attname		as cdt_col
  , a.attnum		as field
  , t.typname		as type
  , na.attnotnull	as nonull		-- notnull of native table
  , pg_get_expr (nd.adbin,nd.adrelid)		as def	--PG 12+

  , case when a.attlen < 0 then null else a.attlen end 	as length
  , coalesce(na.attnum = any((select conkey from pg_constraint
        where connamespace = nc.relnamespace
        and conrelid = nc.oid and contype = 'p')::int4[]),'f') as is_pkey
  , ts.pkey		-- like ispkey, but can be overridden explicitly in the wms file
  , c.relkind		as tab_kind
  , ts.nat_sch
  , ts.nat_tab
  , ts.nat_col
  from			pg_class	c
      join		pg_attribute	a	on a.attrelid =	c.oid
      join		pg_type		t	on t.oid = a.atttypid
      join		pg_namespace	n	on n.oid = c.relnamespace
      left join		wm.column_native ts	on ts.cnt_sch = n.nspname and ts.cnt_tab = c.relname and ts.cnt_col = a.attname
      left join		pg_namespace	nn	on nn.nspname = ts.nat_sch
      left join		pg_class	nc	on nc.relnamespace = nn.oid and nc.relname = ts.nat_tab
      left join		pg_attribute	na	on na.attrelid = nc.oid and na.attname = a.attname
      left join		pg_attrdef	nd	on nd.adrelid = na.attrelid and nd.adnum = na.attnum
  where c.relkind in ('r','v');
;
grant select on table wm.column_data to public;
create view wm.column_istyle as select
    coalesce(cs.cs_sch, zs.cs_sch)		as cs_sch
  , coalesce(cs.cs_tab, zs.cs_tab)		as cs_tab
  , coalesce(cs.cs_sch, zs.cs_sch) || '.' || coalesce(cs.cs_tab, zs.cs_tab)		as cs_obj
  , coalesce(cs.cs_col, zs.cs_col)		as cs_col
  , coalesce(cs.sw_name, zs.sw_name)		as sw_name
  , coalesce(cs.sw_value, zs.sw_value)		as sw_value
  , cs.sw_value					as cs_value
  , zs.nat_sch					as nat_sch
  , zs.nat_tab					as nat_tab
  , zs.nat_col					as nat_col
  , zs.sw_value					as nat_value

  from		wm.column_style  cs
  full join	( select nn.cnt_sch as cs_sch, nn.cnt_tab as cs_tab, nn.cnt_col as cs_col, ns.sw_name, ns.sw_value, nn.nat_sch, nn.nat_tab, nn.nat_col
    from	wm.column_native nn
    join	wm.column_style  ns	on ns.cs_sch = nn.nat_sch and ns.cs_tab = nn.nat_tab and ns.cs_col = nn.nat_col
  )		as		 zs	on zs.cs_sch = cs.cs_sch and zs.cs_tab = cs.cs_tab and zs.cs_col = cs.cs_col and zs.sw_name = cs.sw_name;
create index wm_column_native_x_nat_sch_nat_tab on wm.column_native (nat_sch,nat_tab);
create view wm.fkey_pub as select
    tn.cnt_sch				as tt_sch
  , tn.cnt_tab				as tt_tab
  , tn.cnt_sch || '.' || tn.cnt_tab	as tt_obj
  , tn.cnt_col				as tt_col
  , tn.nat_sch				as tn_sch
  , tn.nat_tab				as tn_tab
  , tn.nat_sch || '.' || tn.nat_tab	as tn_obj
  , tn.nat_col				as tn_col
  , fn.cnt_sch				as ft_sch
  , fn.cnt_tab				as ft_tab
  , fn.cnt_sch || '.' || fn.cnt_tab	as ft_obj
  , fn.cnt_col				as ft_col
  , fn.nat_sch				as fn_sch
  , fn.nat_tab				as fn_tab
  , fn.nat_sch || '.' || fn.nat_tab	as fn_obj
  , fn.nat_col				as fn_col
  , kd.key
  , kd.keys
  , kd.conname
  , case when exists (select * from wm.column_native where cnt_sch = tn.cnt_sch and cnt_tab = tn.cnt_tab and nat_sch = tn.nat_sch and nat_tab = tn.nat_tab and cnt_col != tn.cnt_col and nat_col = kd.kyt_col) then
        tn.cnt_col
    else
        null
    end						as unikey

  from	wm.fkey_data	kd
    join		wm.column_native	tn on tn.nat_sch = kd.kyt_sch and tn.nat_tab = kd.kyt_tab and tn.nat_col = kd.kyt_col
    join		wm.column_native	fn on fn.nat_sch = kd.kyf_sch and fn.nat_tab = kd.kyf_tab and fn.nat_col = kd.kyf_col
  where	not kd.kyt_sch in ('pg_catalog','information_schema');
grant select on table wm.fkey_pub to public;
create view wm.fkeys_data as select
      co.conname				as conname
    , tn.nspname				as kst_sch
    , tc.relname				as kst_tab
    , wm.column_names(co.conrelid,co.conkey)	as kst_cols
    , fn.nspname				as ksf_sch
    , fc.relname				as ksf_tab
    , wm.column_names(co.confrelid,co.confkey)	as ksf_cols
  from			pg_constraint	co 
    join		pg_class	tc on tc.oid = co.conrelid
    join		pg_namespace	tn on tn.oid = tc.relnamespace
    join		pg_class	fc on fc.oid = co.confrelid
    join		pg_namespace	fn on fn.oid = fc.relnamespace
  where co.contype = 'f';
grant select on table wm.fkeys_data to public;
create function wylib.data_tf_notify() returns trigger language plpgsql security definer as $$
    declare
      trec	record;
    begin
      if TG_OP = 'DELETE' then trec = old; else trec = new; end if;
      perform pg_notify('wylib', format('{"target":"data", "component":"%s", "name":"%s", "oper":"%s"}', trec.component, trec.name, TG_OP));
      return null;
    end;
$$;
create table base.ent (
id		text		primary key
  , ent_num	int		not null check(ent_num > 0)
  , ent_type	varchar(1)	not null default 'p' check(ent_type in ('p','o','g','r'))
  , ent_name	text		not null
  , fir_name	text		constraint "!base.ent.CFN" check(case when ent_type != 'p' then fir_name is null end)
  , mid_name	text		constraint "!base.ent.CMN" check(case when fir_name is null then mid_name is null end)
  , pref_name	text		constraint "!base.ent.CPN" check(case when fir_name is null then pref_name is null end)
  , title	text		constraint "!base.ent.CTI" check(case when fir_name is null then title is null end)
  , gender	varchar(1)	constraint "!base.ent.CGN" check(case when ent_type != 'p' then gender is null end)
  , marital	varchar(1)	constraint "!base.ent.CMS" check(case when ent_type != 'p' then marital is null end)
  , ent_cmt	text
  , born_date	date
  , username	text		unique
  , conn_pub	jsonb
  , ent_inact	boolean		not null default false
  , country	varchar(3)	not null default 'US' references base.country on update cascade
  , tax_id	text          , unique(country, tax_id)
  , bank	text
  , _last_addr	int		not null default 0	-- leading '_' makes these invisible to multiview triggers
  , _last_comm	int		not null default 0



    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create view base.language_v as select l.*,
  tt.count as tables,
  ct.count as columns,
  vt.count as values,
  mt.count as messages
  
  from		base.language	l
  left join	(select language, count(title) from wm.table_text group by 1) tt
  		on tt.language = l.code
  left join	(select language, count(title) from wm.column_text group by 1) ct
  		on ct.language = l.code
  left join	(select language, count(title) from wm.value_text group by 1) vt
  		on vt.language = l.code
  left join	(select language, count(title) from wm.message_text group by 1) mt
  		on mt.language = l.code;
grant select on table base.language_v to public;
create function base.priv_has(priv text, lev int) returns boolean language sql stable as $$
      select base.priv_role(session_user, priv, lev);
$$;
create view wm.column_lang as select
    cd.cdt_sch					as sch
  , cd.cdt_tab					as tab
  , cd.cdt_sch || '.' || cd.cdt_tab		as obj
  , cd.cdt_col					as col
  , cd.nat_sch
  , cd.nat_tab
  , cd.nat_sch || '.' || cd.nat_tab		as nat
  , cd.nat_col
  , (select array_agg(to_jsonb(d)) from (select value, title, help from wm.value_text vt where vt.vt_sch = cd.nat_sch and vt.vt_tab = cd.nat_tab and vt.vt_col = cd.nat_col and vt.language = nt.language order by value) d) as values
  , coalesce(ct.language, nt.language, 'eng')	as language
  , coalesce(ct.title, nt.title, cd.cdt_col)	as title
  , coalesce(ct.help, nt.help)			as help
  , cd.cdt_sch in ('pg_catalog','information_schema') as system
  from		wm.column_data cd
    left join	wm.column_text nt	on nt.ct_sch = cd.nat_sch and nt.ct_tab = cd.nat_tab and nt.ct_col = cd.nat_col
    left join	wm.column_text ct	on ct.ct_sch = cd.cdt_sch and ct.ct_tab = cd.cdt_tab and ct.ct_col = cd.cdt_col 	--(No!) and ct.language = nt.language

    where	cd.cdt_col != '_oid'
    and		cd.field >= 0;
grant select on table wm.column_lang to public;
create view wm.column_meta as select
    cd.cdt_sch					as sch
  , cd.cdt_tab					as tab
  , cd.cdt_sch || '.' || cd.cdt_tab		as obj
  , cd.cdt_col					as col
  , cd.field
  , cd.type
  , cd.nonull
  , cd.def
  , cd.length
  , cd.is_pkey
  , cd.pkey
  , cd.nat_sch
  , cd.nat_tab
  , cd.nat_sch || '.' || cd.nat_tab		as nat
  , cd.nat_col
  , (select array_agg(distinct value) from wm.value_text vt where vt.vt_sch = cd.nat_sch and vt.vt_tab = cd.nat_tab and vt.vt_col = cd.nat_col) as values
  , array (select array[sw_name, sw_value] from wm.column_istyle cs where cs.cs_sch = cd.cdt_sch and cs.cs_tab = cd.cdt_tab and cs.cs_col = cd.cdt_col order by sw_name) as styles
  from		wm.column_data cd
    where	cd.cdt_col != '_oid'
    and		cd.field >= 0;
grant select on table wm.column_meta to public;
create view wm.column_pub as select
    cd.cdt_sch					as sch
  , cd.cdt_tab					as tab
  , cd.cdt_sch || '.' || cd.cdt_tab		as obj
  , cd.cdt_col					as col
  , cd.field
  , cd.type
  , cd.nonull
  , cd.def
  , cd.length
  , cd.is_pkey
  , cd.pkey
  , cd.nat_sch
  , cd.nat_tab
  , cd.nat_sch || '.' || cd.nat_tab		as nat
  , cd.nat_col
  , coalesce(vt.language, nt.language, 'eng')	as language
  , coalesce(vt.title, nt.title, cd.cdt_col)	as title
  , coalesce(vt.help, nt.help)			as help
  from		wm.column_data cd
    left join	wm.column_text vt	on vt.ct_sch = cd.cdt_sch and vt.ct_tab = cd.cdt_tab and vt.ct_col = cd.cdt_col
    left join	wm.column_text nt	on nt.ct_sch = cd.nat_sch and nt.ct_tab = cd.nat_tab and nt.ct_col = cd.nat_col

    where	cd.cdt_col != '_oid'
    and		cd.field >= 0;
grant select on table wm.column_pub to public;
create function wm.default_native() returns int language plpgsql as $$
    declare
        crec	record;
        nrec	record;
        sname	varchar;
        tname	varchar;
        cnt	int default 0;
    begin
        delete from wm.column_native;
        for crec in select * from wm.column_data where cdt_col != '_oid' and field  >= 0 and cdt_sch not in ('pg_catalog','information_schema') loop

            sname = crec.cdt_sch;
            tname = crec.cdt_tab;
            loop
                select into nrec * from wm.view_column_usage where view_schema = sname and view_name = tname and column_name = crec.cdt_col order by table_name desc limit 1;
                if not found then exit; end if;
                sname = nrec.table_schema;
                tname = nrec.table_name;
            end loop;
            insert into wm.column_native (cnt_sch, cnt_tab, cnt_col, nat_sch, nat_tab, nat_col, pkey, nat_exp) values (crec.cdt_sch, crec.cdt_tab, crec.cdt_col, sname, tname, crec.cdt_col, crec.is_pkey, false);
            cnt = cnt + 1;
        end loop;
        return cnt;
    end;
$$;
create view wm.fkeys_pub as select
    tn.cnt_sch				as tt_sch
  , tn.cnt_tab				as tt_tab
  , tn.cnt_sch || '.' || tn.cnt_tab	as tt_obj
  , tk.kst_cols				as tt_cols
  , tn.nat_sch				as tn_sch
  , tn.nat_tab				as tn_tab
  , tn.nat_sch || '.' || tn.nat_tab	as tn_obj
  , fn.cnt_sch				as ft_sch
  , fn.cnt_tab				as ft_tab
  , fn.cnt_sch || '.' || fn.cnt_tab	as ft_obj
  , tk.ksf_cols				as ft_cols
  , fn.nat_sch				as fn_sch
  , fn.nat_tab				as fn_tab
  , fn.nat_sch || '.' || fn.nat_tab	as fn_obj
  , tk.conname
  from	wm.fkeys_data		tk
    join		wm.column_native	tn on tn.nat_sch = tk.kst_sch and tn.nat_tab = tk.kst_tab and tn.nat_col = tk.kst_cols[1]
    join		wm.column_native	fn on fn.nat_sch = tk.ksf_sch and fn.nat_tab = tk.ksf_tab and fn.nat_col = tk.ksf_cols[1]
  where	not tk.kst_sch in ('pg_catalog','information_schema');
grant select on table wm.fkeys_pub to public;
create view wm.table_data as select
    ns.nspname				as td_sch
  , cl.relname				as td_tab
  , ns.nspname || '.' || cl.relname	as obj
  , cl.relkind				as tab_kind

  , coalesce(ci.indisprimary,false)	as has_pkey		-- PG 12+
  , cl.relnatts				as cols
  , ns.nspname in ('pg_catalog','information_schema') as system
  , kd.pkey
  from		pg_class	cl
  join		pg_namespace	ns	on cl.relnamespace = ns.oid
  left join	(select cdt_sch,cdt_tab,array_agg(cdt_col) as pkey from (select cdt_sch,cdt_tab,cdt_col,field from wm.column_data where pkey order by 1,2,4) sq group by 1,2) kd on kd.cdt_sch = ns.nspname and kd.cdt_tab = cl.relname
  left join	pg_index	ci	on ci.indrelid = cl.oid and ci.indisprimary
  where		cl.relkind in ('r','v');
create table base.addr (
addr_ent	text		references base.ent on update cascade on delete cascade
  , addr_seq	int	      , primary key (addr_ent, addr_seq)
  , addr_spec	text		not null
  , addr_type	text		not null check(addr_type in ('phys','mail','bill','ship','birth'))
  , addr_prim	boolean		not null default false constraint "!base.addr.CPA" check(case when addr_inact is true then addr_prim is false end)
  , addr_cmt	text
  , addr_inact	boolean		not null default false
  , addr_priv	boolean		not null default false
  , city	text
  , state	text
  , pcode	text
  , country	varchar(3)	constraint "!base.addr.CCO" not null default 'US' references base.country on update cascade
  , unique (addr_ent, addr_seq, addr_type)		-- Needed for addr_prim FK to work
  , constraint "!base.addr.USP" unique (addr_ent, addr_type, addr_spec)

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table base.comm (
comm_ent	text		references base.ent on update cascade on delete cascade
  , comm_seq	int	      , primary key (comm_ent, comm_seq)
  , comm_spec	text		not null
  , comm_type	text		not null check(comm_type in ('phone','email','cell','fax','text','web','pager','other'))
  , comm_prim	boolean		not null default false constraint "!base.comm.CPC" check(case when comm_inact is true then comm_prim is false end)
  , comm_cmt	text
  , comm_inact	boolean		not null default false
  , comm_priv	boolean		not null default false
  , unique (comm_ent, comm_seq, comm_type)		-- Needed for comm_prim FK to work
  , constraint "!base.comm.USP" unique (comm_ent, comm_type, comm_spec)

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.curr_eid() returns text language sql security definer stable as $$
    select id from base.ent where username = session_user;
$$;
create table base.ent_audit (
id text
          , a_seq	int		check (a_seq >= 0)
          , a_date	timestamptz	not null default current_timestamp
          , a_by	name		not null default session_user references base.ent (username) on update cascade
          , a_action	audit_type	not null default 'update'
          , a_values	jsonb
          , primary key (id,a_seq)
);
select wm.create_role('glman_3');
grant select on table base.ent_audit to glman_3;
create table base.ent_link (
org		text		references base.ent on update cascade
  , mem		text		references base.ent on update cascade on delete cascade
  , primary key (org, mem)
  , role	text
  , supr_path	text[]		-- other modules (like empl) are responsible to maintain this cached field
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.ent_tf_dacc() returns trigger language plpgsql as $$
    begin
        if old.username is not null then
            execute 'drop role if exists ' || old.username;
        end if;
        return old;
    end;
$$;
create function base.ent_tf_id() returns trigger language plpgsql as $$
    declare
      min_num	int;
    begin
      if new.ent_num is null then
        lock table base.ent;
        min_num = case when new.ent_type = 'p' then 1000
                       when new.ent_type = 'g' then 100
                       when new.ent_type = 'o' then 500
                       else 1 end;
        select into new.ent_num coalesce(max(ent_num)+1,min_num) from base.ent where ent_type = new.ent_type and ent_num >= min_num;
      end if;
      new.id = new.ent_type || new.ent_num::text;  



      return new;
    end;
$$;
create function base.ent_tf_iuacc() returns trigger language plpgsql security definer as $$
    declare
      trec	record;
    begin
      if new.username is null then		-- Can't have connection access without a username
        new.conn_pub = null;
      end if;
      if TG_OP = 'UPDATE' then			-- if trying to modify an existing username
        if new.username is distinct from old.username then
          if new.username is null then		-- Don't leave relational privs stranded
            delete from base.priv where grantee = old.username;
          end if;
          if old.username is not null then
            execute 'drop role if exists ' || '"' || old.username || '"';
          end if;
        end if;
      end if;

      if new.username is not null and not exists (select rolname from pg_roles where rolname = new.username) then

        execute 'create role ' || '"' || new.username || '" login';
        for trec in select * from base.priv where grantee = new.username loop
          execute 'grant "' || trec.priv_level || '" to ' || trec.grantee;
        end loop;
      end if;
      return new;
    end;
$$;
create view base.ent_v as select e.id, e.ent_num, e.conn_pub, e.ent_name, e.ent_type, e.ent_cmt, e.fir_name, e.mid_name, e.pref_name, e.title, e.gender, e.marital, e.born_date, e.username, e.ent_inact, e.country, e.tax_id, e.bank, e.crt_by, e.mod_by, e.crt_date, e.mod_date
      , case when e.fir_name is null then e.ent_name else e.ent_name || ', ' || coalesce(e.pref_name,e.fir_name) end	as std_name
      , e.ent_name || case when e.fir_name is not null then ', ' || 
                case when e.title is null then '' else e.title || ' ' end ||
                e.fir_name ||
                case when e.mid_name is null then '' else ' ' || e.mid_name end
            else '' end												as frm_name
      , case when e.fir_name is null then '' else coalesce(e.pref_name,e.fir_name) || ' ' end || e.ent_name	as cas_name
      , e.fir_name || case when e.mid_name is null then '' else ' ' || e.mid_name end				as giv_name	
      , extract(year from age(e.born_date))									as age
    from	base.ent	e;

    ;
    ;
    create rule base_ent_v_delete as on delete to base.ent_v
        do instead delete from base.ent where id = old.id;
select wm.create_role('ent_1');
grant select on table base.ent_v to ent_1;
select wm.create_role('ent_2');
grant insert on table base.ent_v to ent_2;
grant update on table base.ent_v to ent_2;
select wm.create_role('ent_3');
grant delete on table base.ent_v to ent_3;
create index base_ent_x_ent_type_ent_num on base.ent (ent_type,ent_num);
create index base_ent_x_username on base.ent (username);
create table base.file (
file_ent	text		references base.ent on update cascade on delete cascade
  , file_seq	int	      , primary key (file_ent, file_seq)
  , file_data	bytea		not null
  , file_type	text		not null check(file_type in ('photo','scan','spread','write','other'))
  , file_prim	boolean		not null default false
  , file_fmt	text		not null
  , file_cmt	text
  , file_priv	boolean		not null default false
  , file_cks	bytea		not null
  , unique (file_ent, file_seq, file_type)		-- Needed for file_prim FK to work
  , constraint "!base.file.USP" unique (file_ent, file_type, file_cks)

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table base.parm (
module	text
  , parm	text
  , primary key (module, parm)
  , type	text		check (type in ('int','date','text','float','boolean'))
  , cmt		text
  , v_int	int		check (type = 'int' and v_int is not null or type != 'int' and v_int is null)
  , v_date	date		check (type = 'date' and v_date is not null or type != 'date' and v_date is null)
  , v_text	text		check (type = 'text' and v_text is not null or type != 'text' and v_text is null)
  , v_float	float		check (type = 'float' and v_float is not null or type != 'float' and v_float is null)
  , v_boolean	boolean		check (type = 'boolean' and v_boolean is not null or type != 'boolean' and v_boolean is null)
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table base.priv (
grantee	text		references base.ent (username) on update cascade on delete cascade
  , priv	text	      , primary key (grantee, priv)
  , level	int		constraint "!base.priv.CLV" check(level > 0 and level < 10)
  , priv_level	text		not null
  , cmt		text
);
create table base.token (
token_ent	text		references base.ent on update cascade on delete cascade
  , token_seq	int	      , primary key (token_ent, token_seq)
  , token	text		not null unique
  , allows	varchar(8)	not null default 'login'
  , used	timestamp
  , expires	timestamp(0)	default current_timestamp + '30 minutes'

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.user_id(text) returns text language sql security definer stable as $$
    select id from base.ent where username = $1;
$$;
create function base.username(text) returns text language sql security definer stable as $$
    select username from base.ent where id = $1;
$$;
create table mychips.agents (
agent	text	primary key
  , agent_key	bytea
  , agent_host	text	constraint "!mychips.tallies:CHR" not null
  , agent_port	int	constraint "!mychips.tallies:CPR" not null
  , agent_ip	inet  , constraint "!mychips.agents:AHP" unique (agent_host, agent_port)
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.contracts (
domain	varchar		not null
  , name	varchar		not null
  , version	int		not null default 1 constraint "!mychips.contracts.BVN" check (version >= 1)
  , language	varchar		not null references base.language on update cascade on delete restrict
  , published	date	      , constraint "!mychips.contracts.PBC" check (published is null or (sections is not null and digest is not null))
  , title	varchar		not null
  , tag		varchar
  , text	varchar
  , digest	bytea
  , sections	jsonb
  , primary key(domain, name, version, language)
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create view wm.column_def as select obj, col, 
    case when def is not null then
      'coalesce($1.' || quote_ident(col) || ',' || def || ') as ' || quote_ident(col)
    else
      '$1.' || col || ' as ' || quote_ident(col)
    end as val
  from wm.column_pub order by obj, field;
create function wm.init_dictionary() returns boolean language plpgsql as $$
    declare
      trec	record;
      s		varchar;
      tarr	varchar[];
      oarr	varchar[];
      narr	varchar[];
    begin
      perform wm.default_native();
      for trec in select * from wm.objects where obj_typ = 'view' loop
        foreach s in array trec.col_data loop		-- Overlay user specified natives
          tarr = string_to_array(s,',');
          if tarr[1] != 'nat' then continue; end if;

          oarr = string_to_array(trec.obj_nam,'.');
          narr = string_to_array(tarr[3],'.');
          update wm.column_native set nat_sch = narr[1], nat_tab = narr[2], nat_col = tarr[4], nat_exp = true where cnt_sch = oarr[1] and cnt_tab = oarr[2] and cnt_col = tarr[2];
        end loop;
      end loop;

      for trec in select cdt_sch,cdt_tab,cdt_col from wm.column_data where is_pkey and cdt_col != '_oid' and field >= 0 order by 1,2 loop
        update wm.column_native set pkey = true where cnt_sch = trec.cdt_sch and cnt_tab = trec.cdt_tab and cnt_col = trec.cdt_col;
      end loop;
      
      for trec in select * from wm.objects where obj_typ = 'view' loop
        tarr = string_to_array(trec.col_data[1],',');
        if tarr[1] = 'pri' then			
          tarr = tarr[2:array_upper(tarr,1)];

          oarr = string_to_array(trec.obj_nam,'.');
          update wm.column_native set pkey = (cnt_col = any(tarr)) where cnt_sch = oarr[1] and cnt_tab = oarr[2];
        end if;
      end loop;
      return true;
    end;
  $$;
create view wm.table_lang as select
    td.td_sch				as sch
  , td.td_tab				as tab
  , td.td_sch || '.' || td.td_tab	as obj
  , tt.language
  , tt.title
  , tt.help
  , array (select jsonb_object(array['code', code, 'title', title, 'help', help]) from wm.message_text mt where mt.mt_sch = td.td_sch and mt.mt_tab = td.td_tab and mt.language = tt.language order by code) as messages
  , (select array_agg(to_jsonb(d)) from (select col, title, help, values from wm.column_lang cl where cl.sch = td.td_sch and cl.tab = td.td_tab and cl.language = tt.language) d) as columns
  from		wm.table_data		td
  left join	wm.table_text		tt on td.td_sch = tt.tt_sch and td.td_tab = tt.tt_tab;
grant select on table wm.table_lang to public;
create view wm.table_meta as select
    td.td_sch				as sch
  , td.td_tab				as tab
  , td.td_sch || '.' || td.td_tab	as obj
  , td.tab_kind
  , td.has_pkey
  , td.system
  , to_jsonb(td.pkey)			as pkey
  , td.cols
  , (select jsonb_object_agg(sw_name,sw_value::jsonb) from wm.table_style ts where ts.ts_sch = td.td_sch and ts.ts_tab = td.td_tab) as styles
  , (select array_agg(to_jsonb(d)) from (select col, field, type, nonull, length, pkey, to_jsonb(values) as values, jsonb_object(styles) as styles from wm.column_meta cm where cm.sch = td.td_sch and cm.tab = td.td_tab) d) as columns
  , (select array_agg(to_jsonb(d)) from (select ft_sch || '.' || ft_tab as "table", to_jsonb(tt_cols) as columns, to_jsonb(ft_cols) as foreign from wm.fkeys_pub ks where ks.tt_sch = td.td_sch and ks.tt_tab = td.td_tab) d) as fkeys
  from		wm.table_data		td;
grant select on table wm.table_meta to public;
create view wm.table_pub as select
    td.td_sch				as sch
  , td.td_tab				as tab
  , td.td_sch || '.' || td.td_tab	as obj
  , td.tab_kind
  , td.has_pkey
  , td.pkey
  , td.cols
  , td.system
  , tt.language
  , tt.title
  , tt.help
  from		wm.table_data		td
  left join	wm.table_text		tt on td.td_sch = tt.tt_sch and td.td_tab = tt.tt_tab;
;
grant select on table wm.table_pub to public;
create table base.addr_prim (
prim_ent	text
  , prim_seq	int
  , prim_type	text
  , primary key (prim_ent, prim_seq, prim_type)
  , constraint addr_prim_prim_ent_fk foreign key (prim_ent, prim_seq, prim_type) references base.addr (addr_ent, addr_seq, addr_type)
    on update cascade on delete cascade deferrable
);
create function base.addr_tf_aiud() returns trigger language plpgsql security definer as $$
    begin
        insert into base.addr_prim (prim_ent, prim_seq, prim_type) 
            select addr_ent,max(addr_seq),addr_type from base.addr where not addr_inact and not exists (select * from base.addr_prim cp where cp.prim_ent = addr_ent and cp.prim_type = addr_type) group by 1,3;
        return old;
    end;
$$;
create function base.addr_tf_bd() returns trigger language plpgsql security definer as $$
    begin
        perform base.addr_remove_prim(old.addr_ent, old.addr_seq, old.addr_type);
        return old;
    end;
$$;
create function base.addr_tf_bi() returns trigger language plpgsql security definer as $$
    begin
        if new.addr_seq is null then			-- Generate unique sequence for new address entry
            update base.ent set _last_addr = greatest(coalesce(_last_addr,0) + 1,
              (select coalesce(max(addr_seq),0)+1 from base.addr where addr_ent = new.addr_ent)
            ) where id = new.addr_ent returning _last_addr into new.addr_seq;
            if not found then new.addr_seq = 1; end if;

        end if;
        if new.addr_inact then				-- Can't be primary if inactive
            new.addr_prim = false;
        elsif not exists (select addr_seq from base.addr where addr_ent = new.addr_ent and addr_type = new.addr_type) then
            new.addr_prim = true;
        end if;
        if new.addr_prim then				-- If this is primary, all others are now not
            set constraints base.addr_prim_prim_ent_fk deferred;
            perform base.addr_make_prim(new.addr_ent, new.addr_seq, new.addr_type);
        end if;
        new.addr_prim = false;
        return new;
    end;
$$;
create function base.addr_tf_birth() returns trigger language plpgsql security definer as $$
    begin
      if session_user = 'admin' then
        return new;
      end if;
      if old.addr_type = 'birth' then
        raise exception '!mychips.users:BRM %', old.addr_ent;
        return null;
      end if;
      return new;
    end;
$$;
create function base.addr_tf_bu() returns trigger language plpgsql security definer as $$
    declare
        prim_it		boolean;
    begin
        if new.addr_inact or (not new.addr_prim and old.addr_prim) then	-- Can't be primary if inactive
            prim_it = false;
        elsif new.addr_prim and not old.addr_prim then
            prim_it = true;
        end if;

        if prim_it then
            perform base.addr_make_prim(new.addr_ent, new.addr_seq, new.addr_type);
        elsif not prim_it then
            perform base.addr_remove_prim(new.addr_ent, new.addr_seq, new.addr_type);
        end if;
        new.addr_prim = false;
        return new;
    end;
$$;
create view base.addr_v_flat as select e.id, a0.addr_spec as "phys_addr", a0.city as "phys_city", a0.state as "phys_state", a0.pcode as "phys_pcode", a0.country as "phys_country", a1.addr_spec as "mail_addr", a1.city as "mail_city", a1.state as "mail_state", a1.pcode as "mail_pcode", a1.country as "mail_country", a2.addr_spec as "bill_addr", a2.city as "bill_city", a2.state as "bill_state", a2.pcode as "bill_pcode", a2.country as "bill_country", a3.addr_spec as "ship_addr", a3.city as "ship_city", a3.state as "ship_state", a3.pcode as "ship_pcode", a3.country as "ship_country", a4.addr_spec as "birth_addr", a4.city as "birth_city", a4.state as "birth_state", a4.pcode as "birth_pcode", a4.country as "birth_country" from base.ent e left join base.addr a0 on a0.addr_ent = e.id and a0.addr_type = 'phys' and a0.addr_prim left join base.addr a1 on a1.addr_ent = e.id and a1.addr_type = 'mail' and a1.addr_prim left join base.addr a2 on a2.addr_ent = e.id and a2.addr_type = 'bill' and a2.addr_prim left join base.addr a3 on a3.addr_ent = e.id and a3.addr_type = 'ship' and a3.addr_prim left join base.addr a4 on a4.addr_ent = e.id and a4.addr_type = 'birth' and a4.addr_prim;
create index base_addr_x_addr_type on base.addr (addr_type);
create table base.comm_prim (
prim_ent	text
  , prim_seq	int
  , prim_type	text
  , primary key (prim_ent, prim_seq, prim_type)
  , constraint comm_prim_prim_ent_fk foreign key (prim_ent, prim_seq, prim_type) references base.comm (comm_ent, comm_seq, comm_type)
    on update cascade on delete cascade deferrable
);
create function base.comm_tf_aiud() returns trigger language plpgsql security definer as $$
    begin
        insert into base.comm_prim (prim_ent, prim_seq, prim_type) 
            select comm_ent,max(comm_seq),comm_type from base.comm where not comm_inact and not exists (select * from base.comm_prim cp where cp.prim_ent = comm_ent and cp.prim_type = comm_type) group by 1,3;
        return old;
    end;
$$;
create function base.comm_tf_bd() returns trigger language plpgsql security definer as $$
    begin
        perform base.comm_remove_prim(old.comm_ent, old.comm_seq, old.comm_type);
        return old;
    end;
$$;
create function base.comm_tf_bi() returns trigger language plpgsql security definer as $$
    begin
        if new.comm_seq is null then			-- Generate unique sequence for new communication entry
            update base.ent set _last_comm = greatest(coalesce(_last_comm,0) + 1,
              (select coalesce(max(comm_seq),0)+1 from base.comm where comm_ent = new.comm_ent)
            ) where id = new.comm_ent returning _last_comm into new.comm_seq;
            if not found then new.comm_seq = 1; end if;

        end if;
        if new.comm_inact then				-- Can't be primary if inactive
            new.comm_prim = false;
        elsif not exists (select comm_seq from base.comm where comm_ent = new.comm_ent and comm_type = new.comm_type) then
            new.comm_prim = true;
        end if;
        if new.comm_prim then				-- If this is primary, all others are now not
            set constraints base.comm_prim_prim_ent_fk deferred;
            perform base.comm_make_prim(new.comm_ent, new.comm_seq, new.comm_type);
        end if;
        new.comm_prim = false;
        return new;
    end;
$$;
create function base.comm_tf_bu() returns trigger language plpgsql security definer as $$
    declare
        prim_it		boolean;
    begin
        if new.comm_inact or (not new.comm_prim and old.comm_prim) then	-- Can't be primary if inactive
            prim_it = false;
        elsif new.comm_prim and not old.comm_prim then
            prim_it = true;
        end if;

        if prim_it then
            perform base.comm_make_prim(new.comm_ent, new.comm_seq, new.comm_type);
        elsif not prim_it then
            perform base.comm_remove_prim(new.comm_ent, new.comm_seq, new.comm_type);
        end if;
        new.comm_prim = false;
        return new;
    end;
$$;
create view base.comm_v_flat as select e.id, c0.comm_spec as "phone_comm", c1.comm_spec as "email_comm", c2.comm_spec as "cell_comm", c3.comm_spec as "fax_comm", c4.comm_spec as "text_comm", c5.comm_spec as "web_comm", c6.comm_spec as "pager_comm", c7.comm_spec as "other_comm" from base.ent e left join base.comm c0 on c0.comm_ent = e.id and c0.comm_type = 'phone' and c0.comm_prim left join base.comm c1 on c1.comm_ent = e.id and c1.comm_type = 'email' and c1.comm_prim left join base.comm c2 on c2.comm_ent = e.id and c2.comm_type = 'cell' and c2.comm_prim left join base.comm c3 on c3.comm_ent = e.id and c3.comm_type = 'fax' and c3.comm_prim left join base.comm c4 on c4.comm_ent = e.id and c4.comm_type = 'text' and c4.comm_prim left join base.comm c5 on c5.comm_ent = e.id and c5.comm_type = 'web' and c5.comm_prim left join base.comm c6 on c6.comm_ent = e.id and c6.comm_type = 'pager' and c6.comm_prim left join base.comm c7 on c7.comm_ent = e.id and c7.comm_type = 'other' and c7.comm_prim;
create index base_comm_x_comm_spec on base.comm (comm_spec);
create index base_comm_x_comm_type on base.comm (comm_type);
create function base.ent_audit_tf_bi() --Call when a new audit record is generated
          returns trigger language plpgsql security definer as $$
            begin
                if new.a_seq is null then		--Generate unique audit sequence number
                    select into new.a_seq coalesce(max(a_seq)+1,0) from base.ent_audit where id = new.id;
                end if;
                return new;
            end;
        $$;
create function base.ent_link_tf_check() returns trigger language plpgsql security definer as $$
    declare
        erec	record;
        mrec	record;
    begin
        select into erec * from base.ent where id = new.org;
        
        if erec.ent_type = 'g' then
            return new;
        end if;
        if erec.ent_type = 'p' then
            raise exception '!base.ent_link.NBP % %', new.mem, new.org;
        end if;

        select into mrec * from base.ent where id = new.mem;
        if erec.ent_type = 'c' and mrec.ent_type != 'p' then
            raise exception '!base.ent_link.PBC % %', new.mem, new.org;
        end if;
        return new;
    end;
$$;
create view base.ent_link_v as select el.org, el.mem, el.role, el.supr_path, el.crt_by, el.mod_by, el.crt_date, el.mod_date
      , oe.std_name		as org_name
      , me.std_name		as mem_name
    from	base.ent_link	el
    join	base.ent_v	oe on oe.id = el.org
    join	base.ent_v	me on me.id = el.mem;

    create rule base_ent_link_v_insert as on insert to base.ent_link_v
        do instead insert into base.ent_link (org, mem, role, crt_by, mod_by, crt_date, mod_date) values (new.org, new.mem, new.role, session_user, session_user, current_timestamp, current_timestamp);
    create rule base_ent_link_v_update as on update to base.ent_link_v
        do instead update base.ent_link set role = new.role, mod_by = session_user, mod_date = current_timestamp where org = old.org and mem = old.mem;
    create rule base_ent_link_v_delete as on delete to base.ent_link_v
        do instead delete from base.ent_link where org = old.org and mem = old.mem;
grant select on table base.ent_link_v to ent_1;
grant insert on table base.ent_link_v to ent_2;
grant update on table base.ent_link_v to ent_2;
grant delete on table base.ent_link_v to ent_2;
create function base.ent_tf_audit_d() --Call when a record is deleted in the audited table
          returns trigger language plpgsql security definer as $$
            begin
                insert into base.ent_audit (id,a_date,a_by,a_action,a_values) values (old.id,transaction_timestamp(),session_user,'delete',jsonb_build_object('ent_name',old.ent_name,'ent_type',old.ent_type,'ent_cmt',old.ent_cmt,'fir_name',old.fir_name,'mid_name',old.mid_name,'pref_name',old.pref_name,'title',old.title,'gender',old.gender,'marital',old.marital,'born_date',old.born_date,'username',old.username,'ent_inact',old.ent_inact,'country',old.country,'tax_id',old.tax_id,'bank',old.bank));
                return old;
            end;
        $$;
create function base.ent_tf_audit_u() --Call when a record is updated in the audited table
          returns trigger language plpgsql security definer as $$
            declare
                doit	boolean = false;
                jobj	jsonb = '{}';
            begin
                if new.ent_name is distinct from old.ent_name then doit=true; jobj = jobj || jsonb_build_object('ent_name', old.ent_name); end if;
		if new.ent_type is distinct from old.ent_type then doit=true; jobj = jobj || jsonb_build_object('ent_type', old.ent_type); end if;
		if new.ent_cmt is distinct from old.ent_cmt then doit=true; jobj = jobj || jsonb_build_object('ent_cmt', old.ent_cmt); end if;
		if new.fir_name is distinct from old.fir_name then doit=true; jobj = jobj || jsonb_build_object('fir_name', old.fir_name); end if;
		if new.mid_name is distinct from old.mid_name then doit=true; jobj = jobj || jsonb_build_object('mid_name', old.mid_name); end if;
		if new.pref_name is distinct from old.pref_name then doit=true; jobj = jobj || jsonb_build_object('pref_name', old.pref_name); end if;
		if new.title is distinct from old.title then doit=true; jobj = jobj || jsonb_build_object('title', old.title); end if;
		if new.gender is distinct from old.gender then doit=true; jobj = jobj || jsonb_build_object('gender', old.gender); end if;
		if new.marital is distinct from old.marital then doit=true; jobj = jobj || jsonb_build_object('marital', old.marital); end if;
		if new.born_date is distinct from old.born_date then doit=true; jobj = jobj || jsonb_build_object('born_date', old.born_date); end if;
		if new.username is distinct from old.username then doit=true; jobj = jobj || jsonb_build_object('username', old.username); end if;
		if new.ent_inact is distinct from old.ent_inact then doit=true; jobj = jobj || jsonb_build_object('ent_inact', old.ent_inact); end if;
		if new.country is distinct from old.country then doit=true; jobj = jobj || jsonb_build_object('country', old.country); end if;
		if new.tax_id is distinct from old.tax_id then doit=true; jobj = jobj || jsonb_build_object('tax_id', old.tax_id); end if;
		if new.bank is distinct from old.bank then doit=true; jobj = jobj || jsonb_build_object('bank', old.bank); end if;
		if doit then insert into base.ent_audit (id,a_date,a_by,a_action,a_values) values (old.id,transaction_timestamp(),session_user,'update',jobj); end if;
                return new;
            end;
        $$;
create trigger base_ent_tr_dacc -- do after individual grants are deleted
    after delete on base.ent for each row execute procedure base.ent_tf_dacc();
create trigger base_ent_tr_id before insert or update on base.ent for each row execute procedure base.ent_tf_id();
create trigger base_ent_tr_iuacc before insert or update on base.ent for each row execute procedure base.ent_tf_iuacc();
create function base.ent_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.ent_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.ent (ent_name,ent_type,ent_cmt,fir_name,mid_name,pref_name,title,gender,marital,born_date,username,ent_inact,country,tax_id,bank,crt_by,mod_by,crt_date,mod_date) values (trec.ent_name,trec.ent_type,trec.ent_cmt,trec.fir_name,trec.mid_name,trec.pref_name,trec.title,trec.gender,trec.marital,trec.born_date,trec.username,trec.ent_inact,trec.country,trec.tax_id,trec.bank,session_user,session_user,current_timestamp,current_timestamp) returning id into new.id;
    select into new * from base.ent_v where id = new.id;
    return new;
  end;
$$;
create view base.ent_v_pub as select id, std_name, ent_type, ent_num, username, ent_inact, crt_by, mod_by, crt_date, mod_date from base.ent_v;
grant select on table base.ent_v_pub to public;
create function base.ent_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.ent set ent_name = new.ent_name,ent_cmt = new.ent_cmt,fir_name = new.fir_name,mid_name = new.mid_name,pref_name = new.pref_name,title = new.title,gender = new.gender,marital = new.marital,born_date = new.born_date,username = new.username,ent_inact = new.ent_inact,country = new.country,tax_id = new.tax_id,bank = new.bank,mod_by = session_user,mod_date = current_timestamp where id = old.id returning id into new.id;
    select into new * from base.ent_v where id = new.id;
    return new;
  end;
$$;
create table base.file_prim (
prim_ent	text
  , prim_seq	int
  , prim_type	text
  , primary key (prim_ent, prim_seq, prim_type)
  , constraint file_prim_prim_ent_fk foreign key (prim_ent, prim_seq, prim_type) references base.file (file_ent, file_seq, file_type)
    on update cascade on delete cascade deferrable
);
create function base.file_tf_aiud() returns trigger language plpgsql security definer as $$
    begin
        insert into base.file_prim (prim_ent, prim_seq, prim_type) 
            select file_ent,max(file_seq),file_type from base.file where not exists (select * from base.file_prim cp where cp.prim_ent = file_ent and cp.prim_type = file_type) group by 1,3;
        return old;
    end;
$$;
create function base.file_tf_bd() returns trigger language plpgsql security definer as $$
    begin
        perform base.file_remove_prim(old.file_ent, old.file_seq, old.file_type);
        return old;
    end;
$$;
create function base.file_tf_bi() returns trigger language plpgsql security definer as $$
    begin
        if new.file_seq is null then			-- Generate unique sequence for new entry
            update base.ent set _last_file = greatest(coalesce(_last_file,0) + 1,
              (select coalesce(max(file_seq),0)+1 from base.file where file_ent = new.file_ent)
            ) where id = new.file_ent returning _last_file into new.file_seq;
            if not found then new.file_seq = 1; end if;

        end if;
        if not exists (select file_seq from base.file where file_ent = new.file_ent and file_type = new.file_type) then
            new.file_prim = true;
        end if;
        if new.file_prim then				-- If this is primary, all others are now not
            set constraints base.file_prim_prim_ent_fk deferred;
            perform base.file_make_prim(new.file_ent, new.file_seq, new.file_type);
        end if;
        new.file_prim = false;
        return new;
    end;
$$;
create function base.file_tf_bu() returns trigger language plpgsql security definer as $$
    declare
        prim_it		boolean;
    begin
        if (not new.file_prim and old.file_prim) then
            prim_it = false;
        elsif new.file_prim and not old.file_prim then
            prim_it = true;
        end if;

        if prim_it then
            perform base.file_make_prim(new.file_ent, new.file_seq, new.file_type);
        elsif not prim_it then
            perform base.file_remove_prim(new.file_ent, new.file_seq, new.file_type);
        end if;
        new.file_prim = false;
        return new;
    end;
$$;
create index base_file_x_file_cks on base.file (file_cks);
create index base_file_x_file_type on base.file (file_type);
create table base.parm_audit (
module text,parm text
          , a_seq	int		check (a_seq >= 0)
          , a_date	timestamptz	not null default current_timestamp
          , a_by	name		not null default session_user references base.ent (username) on update cascade
          , a_action	audit_type	not null default 'update'
          , a_values	jsonb
          , primary key (module,parm,a_seq)
);
grant select on table base.parm_audit to glman_3;
create function base.parm_boolean(m text, p text) returns boolean language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'boolean';

        if not found then return null; end if;
        return r.v_boolean;
    end;
$$;
create function base.parm_date(m text, p text) returns date language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'date';

        if not found then return null; end if;
        return r.v_date;
    end;
$$;
create function base.parm_float(m text, p text) returns float language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'float';

        if not found then return null; end if;
        return r.v_float;
    end;
$$;
create function base.parm_int(m text, p text) returns int language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'int';

        if not found then return null; end if;
        return r.v_int;
    end;
$$;
create function base.parm(m text, p text, d anyelement) returns anyelement language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p;
        if not found then return d; end if;
        case when r.type = 'int'	then return r.v_int;
             when r.type = 'date'	then return r.v_date;
             when r.type = 'text'	then return r.v_text;
             when r.type = 'float'	then return r.v_float;
             when r.type = 'boolean'	then return r.v_boolean;
        end case;
    end;
$$;
create function base.parm_text(m text, p text) returns text language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'text';

        if not found then return null; end if;
        return r.v_text;
    end;
$$;
create view base.parm_v as select module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date
  , case when type = 'int'	then v_int::text
         when type = 'date'	then norm_date(v_date)
         when type = 'text'	then v_text
         when type = 'float'	then v_float::text
         when type = 'boolean'	then norm_bool(v_boolean)
    end as value
    from base.parm;
select wm.create_role('glman_1');
grant select on table base.parm_v to glman_1;
select wm.create_role('glman_2');
grant update on table base.parm_v to glman_2;
grant insert on table base.parm_v to glman_3;
grant delete on table base.parm_v to glman_3;
create function base.priv_grants() returns int language plpgsql as $$
    declare
        erec	record;
        trec	record;
        cnt	int default 0;
    begin
        for erec in select * from base.ent where username is not null loop

            if not exists (select usename from pg_shadow where usename = erec.username) then
                execute 'create user ' || erec.username;
            end if;
            for trec in select * from base.priv where grantee = erec.username loop
                execute 'grant "' || trec.priv_level || '" to ' || trec.grantee;
                cnt := cnt + 1;
            end loop;
        end loop;
        return cnt;
    end;
$$;
create function base.priv_tf_dgrp() returns trigger security definer language plpgsql as $$
    begin
        execute 'revoke "' || old.priv_level || '" from ' || old.grantee;
        return old;
    end;
$$;
create function base.priv_tf_iugrp() returns trigger security definer language plpgsql as $$
    begin
        if new.level is null then		-- cache concatenated version of priv name
          new.priv_level = new.priv;
        else
          new.priv_level = new.priv || '_' || new.level;
        end if;
        
        if TG_OP = 'UPDATE' then
            if new.grantee != old.grantee or new.priv != old.priv or new.level is distinct from old.level then
                execute 'revoke "' || old.priv_level || '" from ' || old.grantee;
            end if;
        end if;

        execute 'grant "' || new.priv_level || '" to ' || new.grantee;
        return new;
    end;
$$;
create view base.priv_v as select p.grantee, p.priv, p.level, p.cmt, p.priv_level
  , e.std_name
  , e.username
  , g.priv_list

    from	base.priv	p
    join	base.ent_v	e on e.username = p.grantee
    left join	(select member,array_agg(role) as priv_list from wm.role_members group by 1) g on g.member = p.grantee;

    ;
    ;
    create rule base_priv_v_delete as on delete to base.priv_v
        do instead delete from base.priv where grantee = old.grantee and priv = old.priv;
grant select on table base.priv_v to public;
select wm.create_role('privedit_1');
grant select on table base.priv_v to privedit_1;
select wm.create_role('privedit_2');
grant insert on table base.priv_v to privedit_2;
grant update on table base.priv_v to privedit_2;
grant delete on table base.priv_v to privedit_2;
create function base.std_name(name) returns text language sql security definer stable as $$
    select std_name from base.ent_v where username = $1;
$$;
create function base.std_name(text) returns text language sql security definer stable as $$
    select std_name from base.ent_v where id = $1;
$$;
create function base.token_tf_seq() returns trigger security definer language plpgsql as $$
    begin
      if new.token_seq is null then	-- technically not safe for concurrency, but we should really only have one token being created at a time anyway
        select into new.token_seq coalesce(max(token_seq),0)+1 from base.token where token_ent = new.token_ent;
      end if;
      if new.token is null then				-- If no token specified
        loop
          select into new.token md5(random()::text);
          if not exists (select token from base.token where token = new.token) then
            exit;
          end if;
        end loop;
      end if;
      return new;
    end;
$$;
create view base.token_v as select t.token_ent, t.token_seq, t.token, t.allows, t.used, t.expires, t.crt_by, t.mod_by, t.crt_date, t.mod_date
      , t.expires <= current_timestamp as "expired"
      , t.expires > current_timestamp and used is null as "valid"
      , e.username
      , e.std_name

    from	base.token	t
    join	base.ent_v	e	on e.id = t.token_ent

    ;
create function mychips.agents_tf_biu() returns trigger language plpgsql security definer as $$
    declare
      doupdate boolean = (TG_OP = 'INSERT');
    begin
      if TG_OP = 'UPDATE' then
        if new.agent != old.agent then doupdate = true; end if;
      end if;
      if doupdate then
        begin new.agent_key = mychips.b64v2ba(new.agent);
        exception when others then		-- Ignore errors
          new.agent_key = null;
        end;
      end if;
      return new;
    end;
$$;
create view mychips.agents_v as select a.agent, a.agent_key, a.agent_host, a.agent_port, a.agent_ip
    , agent_host ||':'|| agent_port			as sock
    , agent ||'@'|| agent_host ||':'|| agent_port	as atsock
    , jsonb_build_object(
      'agent', agent, 'host', agent_host, 'port', agent_port
    )							as json
    , not agent_key isnull				as valid
    
    from	mychips.agents a;

    ;
    ;
    create rule mychips_agents_v_delete as on delete to mychips.agents_v
        do instead delete from mychips.agents where agent = old.agent;
create function mychips.contract_json(c mychips.contracts) returns jsonb stable language sql as $$
    select jsonb_strip_nulls(jsonb_build_object(
        'domain',	c.domain
      , 'name',		c.name
      , 'version',	c.version
      , 'language',	c.language
      , 'published',	c.published
      , 'title',	c.title
      , 'tag',		c.tag
      , 'text',		c.text
      , 'sections',	c.sections
    ))
$$;
create function mychips.contracts_tf_bi() returns trigger language plpgsql security definer as $$
    begin
      if new.version is null then
        select into new.version coalesce(version,0)+1 from mychips.contracts where domain = new.domain and name = new.name and version = new.version and language = new.language;
      end if;
      return new;
    end;
$$;
create table mychips.users (
user_ent	text		primary key references base.ent on update cascade on delete cascade
  , user_host	text
  , user_port	int		
  , user_stat	varchar		not null default 'lck' constraint "!mychips.users:UST" check (user_stat in ('act','lck','off'))
  , user_hid	text		

  , peer_cid	text		not null, unique (peer_cid, peer_agent)
  , peer_agent	text	        references mychips.agents on update cascade on delete restrict
  , peer_psig	text
  , peer_named	text
  
  , user_cmt	varchar
  , _last_tally	int		not null default 0
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table wylib.data (
ruid	serial primary key
  , component	text
  , name	text
  , descr	text
  , access	varchar(5)	not null default 'read' constraint "!wylib.data:IAT" check (access in ('priv', 'read', 'write'))
  , owner	text		not null default base.curr_eid() references base.ent on update cascade on delete cascade
  , data	jsonb
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.addr_make_prim(ent text, seq int, typ text) returns void language plpgsql security definer as $$
    begin

        update base.addr_prim set prim_seq = seq where prim_ent = ent and prim_type = typ;
        if not found then
            insert into base.addr_prim (prim_ent,prim_seq,prim_type) values (ent,seq,typ);
        end if;
    end;
$$;
create function base.addr_remove_prim(ent text, seq int, typ text) returns void language plpgsql security definer as $$
    declare
        prim_rec	record;
        addr_rec	record;
    begin

        select * into prim_rec from base.addr_prim where prim_ent = ent and prim_seq = seq and prim_type = typ;
        if found then			-- If the addr we are deleting was a primary, find the next latest record
            select * into addr_rec from base.addr where addr_ent = prim_rec.prim_ent and addr_type = prim_rec.prim_type and addr_seq != seq and not addr_inact order by addr_seq desc limit 1;
            if found then		-- And make it the new primary

                update base.addr_prim set prim_seq = addr_rec.addr_seq where prim_ent = addr_rec.addr_ent and prim_type = addr_rec.addr_type;
            else

                delete from base.addr_prim where prim_ent = ent and prim_seq = seq and prim_type = typ;
            end if;
        else

        end if;
    end;
$$;
create trigger base_addr_tr_aiud after insert or update or delete on base.addr for each statement execute procedure base.addr_tf_aiud();
create trigger base_addr_tr_bd before delete on base.addr for each row execute procedure base.addr_tf_bd();
create trigger base_addr_tr_bi before insert on base.addr for each row execute procedure base.addr_tf_bi();
create trigger base_addr_tr_birth before update on base.addr for each row execute procedure base.addr_tf_birth();
create trigger base_addr_tr_bu before update on base.addr for each row execute procedure base.addr_tf_bu();
create view base.addr_v as select a.addr_ent, a.addr_seq, a.addr_spec, a.city, a.state, a.pcode, a.country, a.addr_cmt, a.addr_type, a.addr_inact, a.addr_priv, a.crt_by, a.mod_by, a.crt_date, a.mod_date
      , oe.std_name
      , ap.prim_seq is not null and ap.prim_seq = a.addr_seq	as addr_prim

    from	base.addr	a
    join	base.ent_v	oe	on oe.id = a.addr_ent
    left join	base.addr_prim	ap	on ap.prim_ent = a.addr_ent and ap.prim_type = a.addr_type;

    ;
    ;
    create rule base_addr_v_delete as on delete to base.addr_v
        do instead delete from base.addr where addr_ent = old.addr_ent and addr_seq = old.addr_seq;
grant select on table base.addr_v to ent_1;
grant insert on table base.addr_v to ent_2;
grant update on table base.addr_v to ent_2;
grant delete on table base.addr_v to ent_3;
create function base.comm_make_prim(ent text, seq int, typ text) returns void language plpgsql security definer as $$
    begin

        update base.comm_prim set prim_seq = seq where prim_ent = ent and prim_type = typ;
        if not found then
            insert into base.comm_prim (prim_ent,prim_seq,prim_type) values (ent,seq,typ);
        end if;
    end;
$$;
create function base.comm_remove_prim(ent text, seq int, typ text) returns void language plpgsql security definer as $$
    declare
        prim_rec	record;
        comm_rec	record;
    begin

        select * into prim_rec from base.comm_prim where prim_ent = ent and prim_seq = seq and prim_type = typ;
        if found then			-- If the comm we are deleting was a primary, find the next latest record
            select * into comm_rec from base.comm where comm_ent = prim_rec.prim_ent and comm_type = prim_rec.prim_type and comm_seq != seq and not comm_inact order by comm_seq desc limit 1;
            if found then		-- And make it the new primary

                update base.comm_prim set prim_seq = comm_rec.comm_seq where prim_ent = comm_rec.comm_ent and prim_type = comm_rec.comm_type;
            else

                delete from base.comm_prim where prim_ent = ent and prim_seq = seq and prim_type = typ;
            end if;
        else

        end if;
    end;
$$;
create trigger base_comm_tr_aiud after insert or update or delete on base.comm for each statement execute procedure base.comm_tf_aiud();
create trigger base_comm_tr_bd before delete on base.comm for each row execute procedure base.comm_tf_bd();
create trigger base_comm_tr_bi before insert on base.comm for each row execute procedure base.comm_tf_bi();
create trigger base_comm_tr_bu before update on base.comm for each row execute procedure base.comm_tf_bu();
create view base.comm_v as select c.comm_ent, c.comm_seq, c.comm_type, c.comm_spec, c.comm_cmt, c.comm_inact, c.comm_priv, c.crt_by, c.mod_by, c.crt_date, c.mod_date
      , oe.std_name
      , cp.prim_seq is not null and cp.prim_seq = c.comm_seq	as comm_prim

    from	base.comm	c
    join	base.ent_v	oe	on oe.id = c.comm_ent
    left join	base.comm_prim	cp	on cp.prim_ent = c.comm_ent and cp.prim_type = c.comm_type;

    ;
    ;
    create rule base_comm_v_delete as on delete to base.comm_v
        do instead delete from base.comm where comm_ent = old.comm_ent and comm_seq = old.comm_seq;
grant select on table base.comm_v to ent_1;
grant insert on table base.comm_v to ent_2;
grant update on table base.comm_v to ent_2;
grant delete on table base.comm_v to ent_3;
create trigger base_ent_audit_tr_bi before insert on base.ent_audit for each row execute procedure base.ent_audit_tf_bi();
create trigger base_ent_link_tf_check before insert or update on base.ent_link for each row execute procedure base.ent_link_tf_check();
create trigger base_ent_tr_audit_d after delete on base.ent for each row execute procedure base.ent_tf_audit_d();
create trigger base_ent_tr_audit_u after update on base.ent for each row execute procedure base.ent_tf_audit_u();
create trigger base_ent_v_tr_ins instead of insert on base.ent_v for each row execute procedure base.ent_v_insfunc();
create trigger base_ent_v_tr_upd instead of update on base.ent_v for each row execute procedure base.ent_v_updfunc();
create function base.file_make_prim(ent text, seq int, typ text) returns void language plpgsql security definer as $$
    begin

        update base.file_prim set prim_seq = seq where prim_ent = ent and prim_type = typ;
        if not found then
            insert into base.file_prim (prim_ent,prim_seq,prim_type) values (ent,seq,typ);
        end if;
    end;
$$;
create function base.file_remove_prim(ent text, seq int, typ text) returns void language plpgsql security definer as $$
    declare
        prim_rec	record;
        file_rec	record;
    begin

        select * into prim_rec from base.file_prim where prim_ent = ent and prim_seq = seq and prim_type = typ;
        if found then			-- If the file we are deleting was a primary, find the next latest record
            select * into file_rec from base.file where file_ent = prim_rec.prim_ent and file_type = prim_rec.prim_type and file_seq != seq order by file_seq desc limit 1;
            if found then		-- And make it the new primary

                update base.file_prim set prim_seq = file_rec.file_seq where prim_ent = file_rec.file_ent and prim_type = file_rec.file_type;
            else

                delete from base.file_prim where prim_ent = ent and prim_seq = seq and prim_type = typ;
            end if;
        else

        end if;
    end;
$$;
create trigger base_file_tr_aiud after insert or update or delete on base.file for each statement execute procedure base.file_tf_aiud();
create trigger base_file_tr_bd before delete on base.file for each row execute procedure base.file_tf_bd();
create trigger base_file_tr_bi before insert on base.file for each row execute procedure base.file_tf_bi();
create trigger base_file_tr_bu before update on base.file for each row execute procedure base.file_tf_bu();
create view base.file_v as select c.file_ent, c.file_seq, c.file_type, c.file_data, c.file_fmt, c.file_cmt, c.file_priv, c.file_cks, c.crt_by, c.mod_by, c.crt_date, c.mod_date
      , oe.std_name
      , cp.prim_seq is not null and cp.prim_seq = c.file_seq	as file_prim

    from	base.file	c
    join	base.ent_v	oe	on oe.id = c.file_ent
    left join	base.file_prim	cp	on cp.prim_ent = c.file_ent and cp.prim_type = c.file_type;

    ;
    ;
    create rule base_file_v_delete as on delete to base.file_v
        do instead delete from base.file where file_ent = old.file_ent and file_seq = old.file_seq;
grant select on table base.file_v to ent_1;
grant insert on table base.file_v to ent_2;
grant update on table base.file_v to ent_2;
grant delete on table base.file_v to ent_3;
create function base.parm_audit_tf_bi() --Call when a new audit record is generated
          returns trigger language plpgsql security definer as $$
            begin
                if new.a_seq is null then		--Generate unique audit sequence number
                    select into new.a_seq coalesce(max(a_seq)+1,0) from base.parm_audit where module = new.module and parm = new.parm;
                end if;
                return new;
            end;
        $$;
create function base.parmset(m text, p text, v anyelement, t text default null) returns anyelement language plpgsql as $$
    begin
      if exists (select type from base.parm where module = m and parm = p) then
        update base.parm_v set value = v where module = m and parm = p;
      else
        insert into base.parm_v (module,parm,value,type) values (m,p,v,t);
      end if;
      return v;
    end;
$$;
create function base.parm(m text, p text) returns text language sql stable as $$ select value from base.parm_v where module = m and parm = p; $$;
create function base.parm_tf_audit_d() --Call when a record is deleted in the audited table
          returns trigger language plpgsql security definer as $$
            begin
                insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_values) values (old.module, old.parm,transaction_timestamp(),session_user,'delete',jsonb_build_object('cmt',old.cmt,'v_int',old.v_int,'v_date',old.v_date,'v_text',old.v_text,'v_float',old.v_float,'v_boolean',old.v_boolean));
                return old;
            end;
        $$;
create function base.parm_tf_audit_u() --Call when a record is updated in the audited table
          returns trigger language plpgsql security definer as $$
            declare
                doit	boolean = false;
                jobj	jsonb = '{}';
            begin
                if new.cmt is distinct from old.cmt then doit=true; jobj = jobj || jsonb_build_object('cmt', old.cmt); end if;
		if new.v_int is distinct from old.v_int then doit=true; jobj = jobj || jsonb_build_object('v_int', old.v_int); end if;
		if new.v_date is distinct from old.v_date then doit=true; jobj = jobj || jsonb_build_object('v_date', old.v_date); end if;
		if new.v_text is distinct from old.v_text then doit=true; jobj = jobj || jsonb_build_object('v_text', old.v_text); end if;
		if new.v_float is distinct from old.v_float then doit=true; jobj = jobj || jsonb_build_object('v_float', old.v_float); end if;
		if new.v_boolean is distinct from old.v_boolean then doit=true; jobj = jobj || jsonb_build_object('v_boolean', old.v_boolean); end if;
		if doit then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_values) values (old.module, old.parm,transaction_timestamp(),session_user,'update',jobj); end if;
                return new;
            end;
        $$;
create function base.parm_v_tf_del() returns trigger language plpgsql as $$
    begin
        delete from base.parm where module = old.module and parm = old.parm;
        return old;
    end;
$$;
create function base.parm_v_tf_ins() returns trigger language plpgsql as $$
    begin
        if new.type is null then
            case when new.value ~ '^[0-9]+$' then
                new.type = 'int';
            when new.value ~ '^[0-9]+\.*[0-9]*$' then
                new.type = 'float';
            when is_date(new.value) then
                new.type = 'date';
            when lower(new.value) in ('t','f','true','false','yes','no') then
                new.type = 'boolean';
            else
                new.type = 'text';
            end case;
        end if;
    
        case when new.type = 'int' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_int) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value::int);
        when new.type = 'date' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_date) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value::date);
        when new.type = 'float' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_float) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value::float);
        when new.type = 'boolean' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_boolean) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value::boolean);
        else		-- when new.type = 'text' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_text) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value);
        end case;
        return new;
    end;
$$;
create function base.parm_v_tf_upd() returns trigger language plpgsql as $$
    begin
        case when old.type = 'int' then
            update base.parm set parm = new.parm, cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_int = new.value::int where module = old.module and parm = old.parm;
        when old.type = 'date' then
            update base.parm set parm = new.parm, cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_date = new.value::date where module = old.module and parm = old.parm;
        when old.type = 'text' then
            update base.parm set parm = new.parm, cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_text = new.value::text where module = old.module and parm = old.parm;
        when old.type = 'float' then
            update base.parm set parm = new.parm, cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_float = new.value::float where module = old.module and parm = old.parm;
        when old.type = 'boolean' then
            update base.parm set parm = new.parm, cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_boolean = new.value::boolean where module = old.module and parm = old.parm;
        end case;
        return new;
    end;
$$;
create function base.pop_role(rname text) returns void security definer language plpgsql as $$
    declare
      trec	record;
    begin
      for trec in select grantee from base.priv_v where priv = rname and level is null loop
        if not exists (select from pg_catalog.pg_roles where rolname = trec.grantee) then
          execute 'create role ' || '"' || trec.grantee || '" login';
        end if;
        execute 'grant ' || rname || ' to ' || trec.grantee;
      end loop;
    end;
$$;
create trigger base_priv_tr_dgrp before delete on base.priv for each row execute procedure base.priv_tf_dgrp();
create trigger base_priv_tr_iugrp before insert or update on base.priv for each row execute procedure base.priv_tf_iugrp();
create function base.priv_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.priv_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.priv (grantee,priv,level,cmt) values (new.grantee,new.priv,trec.level,trec.cmt) returning grantee,priv into new.grantee, new.priv;
    select into new * from base.priv_v where grantee = new.grantee and priv = new.priv;
    return new;
  end;
$$;
create function base.priv_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.priv set grantee = new.grantee,priv = new.priv,level = new.level,cmt = new.cmt where grantee = old.grantee and priv = old.priv returning grantee,priv into new.grantee, new.priv;
    select into new * from base.priv_v where grantee = new.grantee and priv = new.priv;
    return new;
  end;
$$;
create trigger base_token_tr_seq before insert on base.token for each row execute procedure base.token_tf_seq();
create function base.token_valid(uname text, tok text, pub jsonb) returns boolean language plpgsql as $$
    declare
      trec	record;
    begin
      select into trec valid,token,allows,token_ent,token_seq from base.token_v where username = uname and allows = 'login' order by token_seq desc limit 1;
      if found and trec.valid and tok = trec.token then
        update base.token set used = current_timestamp where token_ent = trec.token_ent and token_seq = trec.token_seq;
        if (pub->'tag') notnull and (pub->'key') notnull then		-- Remember user's new public key
          update base.ent set conn_pub[tag] = (pub->'key') where id = trec.token_ent;
        else
          update base.ent set conn_pub = pub where id = trec.token_ent;
        end if;
        return true;
      end if;
      return false;
    end;
$$;
create function base.token_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.token_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.token (token_ent,allows,crt_by,mod_by,crt_date,mod_date) values (new.token_ent,trec.allows,session_user,session_user,current_timestamp,current_timestamp) returning token_ent,token_seq into new.token_ent, new.token_seq;
    select into new * from base.token_v where token_ent = new.token_ent and token_seq = new.token_seq;
    return new;
  end;
$$;
create view base.token_v_ticket as select token_ent, allows, token, expires
      , base.parm_text('wyseman','host') as host
      , base.parm_int('wyseman','port') as port
    from	base.token	t;
create trigger mychips_agents_tr_biu before insert or update on mychips.agents for each row execute procedure mychips.agents_tf_biu();
create function mychips.agents_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.agents_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.agents (agent,agent_host,agent_port,crt_by,mod_by,crt_date,mod_date) values (new.agent,trec.agent_host,trec.agent_port,session_user,session_user,current_timestamp,current_timestamp) returning agent into new.agent;
    select into new * from mychips.agents_v where agent = new.agent;
    return new;
  end;
$$;
create function mychips.agents_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.agents set agent_host = new.agent_host,agent_port = new.agent_port,agent_ip = new.agent_ip,mod_by = session_user,mod_date = current_timestamp where agent = old.agent returning agent into new.agent;
    select into new * from mychips.agents_v where agent = new.agent;
    return new;
  end;
$$;
create trigger mychips_contracts_tr_bi before insert on mychips.contracts for each row execute procedure mychips.contracts_tf_bi();
create view mychips.contracts_v as select c.domain, c.name, c.version, c.language, c.title, c.text, c.tag, c.digest, c.sections, c.published, c.crt_by, c.mod_by, c.crt_date, c.mod_date
  , mychips.contract_url(c.domain, c.name, c.version, c.language, c.digest::text) as source
  , mychips.contract_json(c)					as json_core
  , mychips.contract_json(c) || jsonb_build_object(
      'digest',		c.digest
    )								as json
  , mychips.j2h(mychips.contract_json(c)) as digest_v
  , mychips.j2h(mychips.contract_json(c)) = coalesce(c.digest,'') as clean
  
    from	mychips.contracts c;

    ;
    ;
    create rule mychips_contracts_v_delete as on delete to mychips.contracts_v
        do instead delete from mychips.contracts where domain = old.domain and name = old.name and version = old.version and language = old.language;
select wm.create_role('contract_1');
grant select on table mychips.contracts_v to contract_1;
select wm.create_role('contract_2');
grant select on table mychips.contracts_v to contract_2;
grant insert on table mychips.contracts_v to contract_2;
grant update on table mychips.contracts_v to contract_2;
select wm.create_role('contract_3');
grant delete on table mychips.contracts_v to contract_3;
create function mychips.parm_tf_change() returns trigger language plpgsql security definer as $$
    declare
      channel	text = 'parm_' || new.module;
      value	text = (select value from base.parm_v where module = new.module and parm = new.parm);
    begin
      perform pg_notify(channel, format('{"target":"%s", "value":"%s", "oper":"%s", "time":"%s"}', new.parm, value, TG_OP, transaction_timestamp()::text));
      return null;
    end;
$$;
create table mychips.tallies (
tally_ent	text		references mychips.users on update cascade on delete cascade
  , tally_seq	int	      , primary key (tally_ent, tally_seq)


  , tally_uuid	uuid		not null
  , tally_type	tally_side	not null default 'stock'
  , tally_date	timestamptz	not null default current_timestamp
  , version	int		not null default 1 constraint "!mychips.tallies:VER" check (version > 0)
  , comment	text
  , contract	jsonb		constraint "!mychips.tallies:TCM" check (not (status = 'open' and contract isnull))
  , hold_cert	jsonb		constraint "!mychips.tallies:UCM" check (not (status = 'open' and hold_cert isnull))
  , part_cert	jsonb		constraint "!mychips.tallies:PCM" check (not (status = 'open' and part_cert isnull))
  , hold_sig	text		constraint "!mychips.tallies:USM" check (not (status = 'open' and hold_sig isnull))
  , part_sig	text		constraint "!mychips.tallies:PSM" check (not (status = 'open' and part_sig isnull))
  , hold_terms	jsonb		not null default '{}'			-- Terms we grant to our partner
  , part_terms	jsonb		not null default '{}'			-- Terms partner grants to our holder
  , digest	bytea


  , target	bigint		not null default 0 constraint "!mychips.tallies:TGT" check (target >= 0 and target <= bound)
  , bound	bigint		not null default 0 constraint "!mychips.tallies:BND" check (bound >= 0)
  , reward	float		not null default 0 constraint "!mychips.tallies:RWD" check (reward >= -1 and reward <= 1)
  , clutch	float		not null default 0 constraint "!mychips.tallies:CLT" check (clutch >= -1 and clutch <= 1)


  , request	text		constraint "!mychips.tallies:IVR" check(request is null or request in ('void','draft','offer','open'))
  , status	text		not null default 'draft'
  				constraint "!mychips.tallies:IVS" check(status in ('void','draft','offer','open','close'))
  , part_ent	text		references mychips.users on update cascade on delete restrict
  				constraint "!mychips.tallies:NSP" check (part_ent != tally_ent)
  			      , constraint "!mychips.tallies:TNU" unique(tally_type, tally_uuid)
  , net_c	bigint		default 0 not null
  , net_pc	bigint		default 0 not null
  , hold_cid	text		constraint "!mychips.tallies:UCI" check (not (status = 'open' and hold_cid isnull))
  , part_cid	text		constraint "!mychips.tallies:PCI" check (not (status = 'open' and part_cid isnull))
  , hold_agent	text		references mychips.agents on update restrict on delete restrict
  				constraint "!mychips.tallies:UAI" check (not (status = 'open' and hold_agent isnull))
  , part_agent	text		references mychips.agents on update restrict on delete restrict
  				constraint "!mychips.tallies:PAI" check (not (status = 'open' and part_agent isnull))
  , hold_sets	jsonb		not null default '{}'
  , part_sets	jsonb		not null default '{}'
  , chain_conf	int		not null default 0
  , chain_stat	text		not null default 'con' check (chain_stat in ('con','prob','req','err','pend'))
  , _last_chit	int		not null default 0





    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function mychips.users_tf_biu() returns trigger language plpgsql security definer as $$
    begin
      if new.user_hid isnull then
        loop
          select into new.user_hid mychips.ba2b64v(decode(lpad(md5(random()::text),12), 'hex'));
          if not exists (select user_ent from mychips.users where user_hid = new.user_hid) then
            exit;
          end if;
        end loop;
      end if;
      if new.peer_cid isnull then			-- Defaults to user ID if not specified
        new.peer_cid = new.user_ent;
      end if;
      return new;
    end;
$$;
create trigger mychips_users_tr_change after insert or update or delete on mychips.users for each statement execute procedure mychips.users_tf_change();
create view mychips.users_v as select 
    ee.id, ee.ent_name, ee.ent_type, ee.ent_cmt, ee.fir_name, ee.mid_name, ee.pref_name, ee.title, ee.gender, ee.marital, ee.born_date, ee.username, ee.ent_inact, ee.country, ee.tax_id, ee.bank, ee.ent_num, ee.std_name, ee.frm_name, ee.giv_name, ee.cas_name, ee.age, ee.conn_pub
  , ue.user_ent, ue.user_host, ue.user_port, ue.user_stat, ue.user_hid, ue.peer_cid, ue.peer_agent, ue.peer_psig, ue.peer_named, ue.user_cmt, ue.crt_by, ue.crt_date, ue.mod_by
  , ag.agent_key, ag.agent_host, ag.agent_port, ag.agent_ip

  , ag.agent_host		as peer_host
  , ag.agent_port		as peer_port







  , greatest(ee.mod_date, ue.mod_date)					as mod_date
  , jsonb_build_object(
      'id',		ee.id
    , 'cid',		ue.peer_cid
    , 'name',		ee.ent_name
    , 'type',		ee.ent_type
    , 'first',		ee.fir_name
    , 'middle',		ee.mid_name
    , 'prefer',		ee.pref_name
    , 'begin',		ee.born_date
    , 'juris',		ee.country
    , 'taxid',		ee.tax_id
    ) as json

    from	base.ent_v	ee
    left join	mychips.users	ue on ue.user_ent = ee.id
    left join	mychips.agents	ag on ag.agent = ue.peer_agent;


    
    
    create rule mychips_users_v_delete_0 as on delete to mychips.users_v do instead nothing;
    create rule mychips_users_v_delete_1 as on delete to mychips.users_v where (old.crt_by = session_user and (current_timestamp - old.crt_date) < '2 hours'::interval) or base.priv_has('userim',3) do instead delete from mychips.users where user_ent = old.user_ent;
select wm.create_role('user_1');
grant select on table mychips.users_v to user_1;
select wm.create_role('user_2');
grant insert on table mychips.users_v to user_2;
grant update on table mychips.users_v to user_2;
select wm.create_role('user_3');
grant delete on table mychips.users_v to user_3;
create trigger wylib_data_tr_notify after insert or update or delete on wylib.data for each row execute procedure wylib.data_tf_notify();
create view wylib.data_v as select wd.ruid, wd.component, wd.name, wd.descr, wd.access, wd.data, wd.owner, wd.crt_by, wd.mod_by, wd.crt_date, wd.mod_date
      , oe.std_name		as own_name

    from	wylib.data	wd
    join	base.ent_v	oe	on oe.id = wd.owner
    where	access = 'read' or owner = base.curr_eid();
grant select on table wylib.data_v to public;
grant insert on table wylib.data_v to public;
grant update on table wylib.data_v to public;
grant delete on table wylib.data_v to public;
create function base.addr_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.addr_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.addr (addr_ent,addr_spec,city,state,pcode,country,addr_cmt,addr_type,addr_prim,addr_inact,addr_priv,crt_by,mod_by,crt_date,mod_date) values (new.addr_ent,trec.addr_spec,trec.city,trec.state,trec.pcode,trec.country,trec.addr_cmt,trec.addr_type,trec.addr_prim,trec.addr_inact,trec.addr_priv,session_user,session_user,current_timestamp,current_timestamp) returning addr_ent,addr_seq into new.addr_ent, new.addr_seq;
    select into new * from base.addr_v where addr_ent = new.addr_ent and addr_seq = new.addr_seq;
    return new;
  end;
$$;
create function base.addr_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.addr set addr_spec = new.addr_spec,city = new.city,state = new.state,pcode = new.pcode,country = new.country,addr_cmt = new.addr_cmt,addr_type = new.addr_type,addr_prim = new.addr_prim,addr_inact = new.addr_inact,addr_priv = new.addr_priv,mod_by = session_user,mod_date = current_timestamp where addr_ent = old.addr_ent and addr_seq = old.addr_seq returning addr_ent,addr_seq into new.addr_ent, new.addr_seq;
    select into new * from base.addr_v where addr_ent = new.addr_ent and addr_seq = new.addr_seq;
    return new;
  end;
$$;
create function base.comm_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.comm_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.comm (comm_ent,comm_type,comm_spec,comm_cmt,comm_inact,comm_priv,comm_prim,crt_by,mod_by,crt_date,mod_date) values (new.comm_ent,trec.comm_type,trec.comm_spec,trec.comm_cmt,trec.comm_inact,trec.comm_priv,trec.comm_prim,session_user,session_user,current_timestamp,current_timestamp) returning comm_ent,comm_seq into new.comm_ent, new.comm_seq;
    select into new * from base.comm_v where comm_ent = new.comm_ent and comm_seq = new.comm_seq;
    return new;
  end;
$$;
create function base.comm_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.comm set comm_type = new.comm_type,comm_spec = new.comm_spec,comm_cmt = new.comm_cmt,comm_inact = new.comm_inact,comm_priv = new.comm_priv,comm_prim = new.comm_prim,mod_by = session_user,mod_date = current_timestamp where comm_ent = old.comm_ent and comm_seq = old.comm_seq returning comm_ent,comm_seq into new.comm_ent, new.comm_seq;
    select into new * from base.comm_v where comm_ent = new.comm_ent and comm_seq = new.comm_seq;
    return new;
  end;
$$;
create function base.file_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.file_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.file (file_ent,file_type,file_data,file_fmt,file_cmt,file_priv,file_prim,file_cks,crt_by,mod_by,crt_date,mod_date) values (new.file_ent,trec.file_type,trec.file_data,trec.file_fmt,trec.file_cmt,trec.file_priv,trec.file_prim,trec.file_cks,session_user,session_user,current_timestamp,current_timestamp) returning file_ent,file_seq into new.file_ent, new.file_seq;
    select into new * from base.file_v where file_ent = new.file_ent and file_seq = new.file_seq;
    return new;
  end;
$$;
create function base.file_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.file set file_type = new.file_type,file_data = new.file_data,file_fmt = new.file_fmt,file_cmt = new.file_cmt,file_priv = new.file_priv,file_prim = new.file_prim,file_cks = new.file_cks,mod_by = session_user,mod_date = current_timestamp where file_ent = old.file_ent and file_seq = old.file_seq returning file_ent,file_seq into new.file_ent, new.file_seq;
    select into new * from base.file_v where file_ent = new.file_ent and file_seq = new.file_seq;
    return new;
  end;
$$;
create trigger base_parm_audit_tr_bi before insert on base.parm_audit for each row execute procedure base.parm_audit_tf_bi();
create function base.parmsett(m text, p text, v text, t text default null) returns text language plpgsql as $$
    begin
      return base.parmset(m,p,v,t);
    end;
$$;
create trigger base_parm_tr_audit_d after delete on base.parm for each row execute procedure base.parm_tf_audit_d();
create trigger base_parm_tr_audit_u after update on base.parm for each row execute procedure base.parm_tf_audit_u();
create trigger base_parm_v_tr_del instead of delete on base.parm_v for each row execute procedure base.parm_v_tf_del();
create trigger base_parm_v_tr_ins instead of insert on base.parm_v for each row execute procedure base.parm_v_tf_ins();
create trigger base_parm_v_tr_upd instead of update on base.parm_v for each row execute procedure base.parm_v_tf_upd();
create trigger base_priv_v_tr_ins instead of insert on base.priv_v for each row execute procedure base.priv_v_insfunc();
create trigger base_priv_v_tr_upd instead of update on base.priv_v for each row execute procedure base.priv_v_updfunc();
create function base.ticket_login(uid text) returns base.token_v_ticket language sql as $$
    insert into base.token_v_ticket (token_ent, allows) values (uid, 'login') returning *;
$$;
create trigger base_token_v_tr_ins instead of insert on base.token_v for each row execute procedure base.token_v_insfunc();
create view json.connect as select
    comm_ent	as "id"
  , comm_seq	as "seq"
  , comm_spec	as "address"
  , comm_type	as "media"
  , comm_prim	as "main"
  , comm_cmt	as "comment"
  , comm_inact	as "prior"
  , comm_priv	as "private"
    from base.comm_v where not comm_ent isnull with cascaded check option;
create view json.contract as select
    domain
  , name
  , version
  , language
  , published
  , title
  , text
  , tag
  , digest
  , sections
    from	mychips.contracts_v;
create view json.file as select
    file_ent	as "id"
  , file_seq	as "seq"
  , file_data	as "data"
  , file_type	as "media"
  , file_fmt	as "format"
  , file_prim	as "main"
  , file_cmt	as "comment"
  , file_priv	as "private"
  , file_cks	as "digest"
    from base.file_v where not file_ent isnull with cascaded check option;
create view json.place as select
    addr_ent	as "id"
  , addr_seq	as "seq"
  , addr_spec	as "address"
  , addr_type	as "type"
  , addr_prim	as "main"
  , city	as "city"
  , state	as "state"
  , pcode	as "post"
  , country	as "country"
  , addr_cmt	as "comment"
  , addr_inact	as "prior"
  , addr_priv	as "private"
    from base.addr_v where not addr_ent is null with cascaded check option;
create view json.user as select
    id		as "id"
  , peer_cid	as "cid"
  , peer_agent	as "agent"
  , ent_name	as "name"
  , ent_type	as "type"
  , fir_name	as "first"
  , mid_name	as "middle"
  , pref_name	as "prefer"
  , born_date	as "begin"
  , peer_named	as "named"
  , country	as "juris"
  , tax_id	as "taxid"
    from mychips.users_v where not user_ent is null with cascaded check option;
create view mychips.addr_v_me as select 
    a.*
    from	base.addr_v a	where addr_ent = base.user_id(session_user);
grant select on table mychips.addr_v_me to user_1;
grant select on table mychips.addr_v_me to user_2;
grant insert on table mychips.addr_v_me to user_2;
grant update on table mychips.addr_v_me to user_2;
grant delete on table mychips.addr_v_me to user_3;
create trigger mychips_agents_v_tr_ins instead of insert on mychips.agents_v for each row execute procedure mychips.agents_v_insfunc();
create trigger mychips_agents_v_tr_upd instead of update on mychips.agents_v for each row execute procedure mychips.agents_v_updfunc();
create view mychips.comm_v_me as select 
    c.*
    from	base.comm_v c	where comm_ent = base.user_id(session_user);
grant select on table mychips.comm_v_me to user_1;
grant select on table mychips.comm_v_me to user_2;
grant insert on table mychips.comm_v_me to user_2;
grant update on table mychips.comm_v_me to user_2;
grant delete on table mychips.comm_v_me to user_3;
create function mychips.contracts_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.contracts_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.contracts (domain,name,version,language,title,text,tag,digest,sections,published,crt_by,mod_by,crt_date,mod_date) values (new.domain,new.name,new.version,new.language,trec.title,trec.text,trec.tag,trec.digest,trec.sections,trec.published,session_user,session_user,current_timestamp,current_timestamp) returning domain,name,version,language into new.domain, new.name, new.version, new.language;
    select into new * from mychips.contracts_v where domain = new.domain and name = new.name and version = new.version and language = new.language;
    return new;
  end;
$$;
create function mychips.contracts_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.contracts set domain = new.domain,name = new.name,version = new.version,language = new.language,title = new.title,text = new.text,tag = new.tag,digest = new.digest,sections = new.sections,published = new.published,mod_by = session_user,mod_date = current_timestamp where domain = old.domain and name = old.name and version = old.version and language = old.language returning domain,name,version,language into new.domain, new.name, new.version, new.language;
    select into new * from mychips.contracts_v where domain = new.domain and name = new.name and version = new.version and language = new.language;
    return new;
  end;
$$;
create view mychips.file_v_me as select 
    f.*
    from	base.file_v f where file_ent = base.user_id(session_user);
grant select on table mychips.file_v_me to user_1;
grant select on table mychips.file_v_me to user_2;
grant insert on table mychips.file_v_me to user_2;
grant update on table mychips.file_v_me to user_2;
grant delete on table mychips.file_v_me to user_3;
create table mychips.lifts (
lift_uuid	uuid
  , lift_seq	int	      , primary key (lift_uuid, lift_seq)


  , request	text		constraint "!mychips.lifts:IVR" check(request isnull or request in ('init','seek','call','relay','found','term','check','good','void'))
  , status	text		not null default 'draft' constraint "!mychips.lifts:IVS" check(status in ('draft','init','seek','call','found','pend','good','void'))
  , tallies	uuid[]		not null
  , lift_type	text		not null default 'rel' constraint "!mychips.lifts:IVT" check(lift_type isnull or lift_type in ('in','org','rel'))
  , circuit	boolean		not null default true


  , units	bigint		not null
  , lift_date	timestamptz	not null default current_timestamp
  , life	interval	not null default '2 minutes'
  , find	jsonb
  , origin	jsonb
  , referee	jsonb

  , digest	bytea		
  , signature	text
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create trigger mychips_parm_tr_change after insert or update on base.parm for each row execute procedure mychips.parm_tf_change();
create table mychips.routes (
rid		serial		primary key
  , via_ent	text		not null	-- Owner of local tally that starts the external route
  , via_tseq	int		not null
  ,				foreign key (via_ent, via_tseq) references mychips.tallies on update cascade on delete cascade
  , dst_cid	text		not null
  , dst_agent	text		not null
  , 				constraint "!mychips.routes:UNI" unique (via_ent, via_tseq, dst_cid, dst_agent)
  , req_ent	text
  , req_tseq	int	      , foreign key (req_ent, req_tseq) references mychips.tallies on update cascade on delete cascade

  , status	text		not null default 'draft' constraint "!mychips.routes:BST" check(status in ('draft','pend','good','none'))
  , step	int		not null default 0 check (step >= 0)
  , lift_count	int		not null default 0 check (step >= 0)
  , lift_date	timestamptz	not null default current_timestamp
  , good_date	timestamptz	not null default current_timestamp

  , min		bigint		not null default 0
  , margin	float		not null default 0 constraint "!mychips.paths:LMG" check (margin >= -1 and margin <= 1)
  , max		bigint		not null default 0
  , reward	float		not null default 0 constraint "!mychips.paths:LRW" check (reward >= -1 and reward <= 1)
);
create trigger mychips_tallies_tr_change after insert or update or delete on mychips.tallies for each statement execute procedure mychips.tallies_tf_change();
create index mychips_tallies_x_tally_date on mychips.tallies (tally_date);
create index mychips_tallies_x_tally_type on mychips.tallies (tally_type);
create index mychips_tallies_x_tally_uuid on mychips.tallies (tally_uuid);
create function mychips.tally_json(te mychips.tallies) returns jsonb stable language sql as $$
    select jsonb_build_object(
       'version',	te.version,
       'uuid',		te.tally_uuid,
       'date',		te.tally_date,
       'comment',	te.comment,
       'agree',		te.contract,
       te.tally_type,	json_build_object(
         'cert',	te.hold_cert,
         'terms',	te.hold_terms
       ),
       case when te.tally_type = 'stock' then 'foil' else 'stock' end, json_build_object(
         'cert',	te.part_cert,
         'terms',	te.part_terms
       )
    )
$$;
create table mychips.tally_tries (
ttry_ent	text	      , primary key (ttry_ent, ttry_seq)
  , ttry_seq	int	      , foreign key (ttry_ent, ttry_seq) references mychips.tallies on update cascade on delete cascade
  , tries	int		not null default 1
  , last	timestamptz	not null default current_timestamp
);
create function mychips.ticket_login(uid text) returns base.token_v_ticket language plpgsql as $$
    declare
      trec	record;
      urec	record;
      retval	jsonb;
    begin
      insert into base.token_v_ticket (token_ent, allows) values (uid, 'login') returning * into trec;
      select into urec * from mychips.users where user_ent = uid;
      trec.host = coalesce(urec.user_host, base.parm_text('mychips','user_host'), trec.host);
      trec.port = coalesce(urec.user_port, base.parm_int('mychips','user_port'), trec.port);
      return trec;
    end;
$$;
create table mychips.tokens (
token_ent	text		references base.ent on update cascade on delete cascade
  , token_seq	int	      , primary key (token_ent, token_seq)
  , token	text		not null unique
  , reuse	boolean		not null default false
  , used	timestamp
  , expires	timestamp(0)	default current_timestamp + '45 minutes'
  , tally_seq	int           , foreign key (token_ent, tally_seq) references mychips.tallies on update cascade on delete cascade
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create trigger mychips_users_tr_biu before insert or update on mychips.users for each row execute procedure mychips.users_tf_biu();
create view mychips.users_v_flat as select 
    u.*
  , a.bill_addr, a.bill_city, a.bill_state, a.bill_pcode, a.bill_country
  , a.ship_addr, a.ship_city, a.ship_state, a.ship_pcode, a.ship_country
  , c.phone_comm, c.cell_comm, c.email_comm, c.web_comm

    from	mychips.users_v		u
    left join	base.addr_v_flat	a on a.id = u.id
    left join	base.comm_v_flat	c on c.id = u.id;
create function mychips.users_vf_post(new mychips.users_v, old mychips.users_v, tgop text) returns mychips.users_v language plpgsql security definer as $$
    begin

      if (tgop = 'INSERT' and new.username is null) then	--Default username to = ID
        new.username = new.id;
        update base.ent set username = new.id where id = new.id;
      end if;




      if new.username is not null and not exists (select * from base.priv where grantee = new.username and priv = 'mychips') then
        insert into base.priv (grantee, priv) values (new.username, 'mychips');
      end if;
      return new;
    end;
$$;
create function mychips.users_vf_pre(new mychips.users_v, old mychips.users_v, tgop text) returns mychips.users_v language plpgsql security definer as $$
    begin

      if not new.peer_agent isnull and not exists (select agent from mychips.agents where agent = new.peer_agent) then
        insert into mychips.agents (agent, agent_host, agent_port) values (new.peer_agent, new.peer_host, new.peer_port);
      end if;
      return new;
    end;
$$;
create function mychips.users_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    nrec mychips.users_v;
    str  varchar;
  begin
    nrec = new; new = mychips.users_vf_pre(nrec, null, TG_OP); if new is null then return null; end if;
    if exists (select id from base.ent where id = new.id) then	-- if primary table record already exists
        update base.ent set mod_by = session_user,mod_date = current_timestamp where id = new.id;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1 and not col ~ $2;' into str using 'base.ent','^_';

        execute 'select ' || str || ';' into trec using new;
        insert into base.ent (ent_name,ent_type,ent_cmt,fir_name,mid_name,pref_name,title,gender,marital,born_date,username,ent_inact,country,tax_id,bank,mod_by,mod_date) values (trec.ent_name,trec.ent_type,trec.ent_cmt,trec.fir_name,trec.mid_name,trec.pref_name,trec.title,trec.gender,trec.marital,trec.born_date,trec.username,trec.ent_inact,trec.country,trec.tax_id,trec.bank,session_user,current_timestamp) returning id into new.id;
    end if;
    
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1 and not col ~ $2;' into str using 'mychips.users','^_';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.users (user_ent,user_host,user_port,user_stat,user_hid,peer_cid,peer_agent,peer_psig,peer_named,user_cmt) values (new.id,trec.user_host,trec.user_port,trec.user_stat,trec.user_hid,trec.peer_cid,trec.peer_agent,trec.peer_psig,trec.peer_named,trec.user_cmt);
    select into new * from mychips.users_v where id = new.id;
    nrec = new; new = mychips.users_vf_post(nrec, null, TG_OP);
    return new;
  end;
$$;
create view mychips.users_v_me as select 
    u.*
    from	mychips.users_v		u where user_ent = base.user_id(session_user);
grant select on table mychips.users_v_me to user_1;
grant select on table mychips.users_v_me to user_2;
grant insert on table mychips.users_v_me to user_2;
grant update on table mychips.users_v_me to user_2;
grant delete on table mychips.users_v_me to user_3;
create function mychips.users_v_updfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    nrec mychips.users_v; orec mychips.users_v;
    str  varchar;
  begin
    nrec = new; orec = old; new = mychips.users_vf_pre(nrec, orec, TG_OP); if new is null then return null; end if;
    update base.ent set ent_name = new.ent_name,ent_cmt = new.ent_cmt,fir_name = new.fir_name,mid_name = new.mid_name,pref_name = new.pref_name,title = new.title,gender = new.gender,marital = new.marital,born_date = new.born_date,username = new.username,ent_inact = new.ent_inact,country = new.country,tax_id = new.tax_id,bank = new.bank,mod_by = session_user,mod_date = current_timestamp where id = old.id returning id into new.id;
    
    
    if exists (select user_ent from mychips.users where user_ent = old.user_ent) then				-- if primary table record already exists
        update mychips.users set user_host = new.user_host,user_port = new.user_port,user_stat = new.user_stat,user_hid = new.user_hid,peer_cid = new.peer_cid,peer_agent = new.peer_agent,peer_psig = new.peer_psig,peer_named = new.peer_named,user_cmt = new.user_cmt,user_ent = new.user_ent,mod_by = session_user,mod_date = current_timestamp where user_ent = old.user_ent;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1 and not col ~ $2;' into str using 'mychips.users','^_';

        execute 'select ' || str || ';' into trec using new;
        insert into mychips.users (user_host,user_port,user_stat,user_hid,peer_cid,peer_agent,peer_psig,peer_named,user_cmt,user_ent,mod_by,mod_date) values (trec.user_host,trec.user_port,trec.user_stat,trec.user_hid,trec.peer_cid,trec.peer_agent,trec.peer_psig,trec.peer_named,trec.user_cmt,new.id,session_user,current_timestamp);
    end if;

    select into new * from mychips.users_v where id = new.id;
    nrec = new; orec = old; new = mychips.users_vf_post(nrec, orec, TG_OP);
    return new;
  end;
$$;
create function wylib.data_v_tf_del() returns trigger language plpgsql security definer as $$
        begin
           if not (old.owner = base.curr_eid() or old.access = 'write') then return null; end if;
            delete from wylib.data where ruid = old.ruid;
            return old;
        end;
    $$;
create function wylib.data_v_tf_ins() returns trigger language plpgsql security definer as $$
        begin

            insert into wylib.data (component, name, descr, access, data, crt_by, mod_by, crt_date, mod_date) values (new.component, new.name, new.descr, new.access, new.data, session_user, session_user, current_timestamp, current_timestamp) returning into new.ruid ruid;
            return new;
        end;
    $$;
create function wylib.data_v_tf_upd() returns trigger language plpgsql security definer  as $$
        begin
           if not (old.owner = base.curr_eid() or old.access = 'write') then return null; end if;
            if ((new.access is not distinct from old.access) and (new.name is not distinct from old.name) and (new.descr is not distinct from old.descr) and (new.data is not distinct from old.data)) then return null; end if;
            update wylib.data set access = new.access, name = new.name, descr = new.descr, data = new.data, mod_by = session_user, mod_date = current_timestamp where ruid = old.ruid returning into new.ruid ruid;
            return new;
        end;
    $$;
create function wylib.get_data(comp text, nam text, own text) returns jsonb language sql stable as $$
      select data from wylib.data_v where owner = coalesce(own,base.curr_eid()) and component = comp and name = nam;
$$;
create function wylib.set_data(comp text, nam text, des text, own text, dat jsonb) returns int language plpgsql as $$
    declare
      userid	text = coalesce(own, base.curr_eid());
      id	int;
      trec	record;
    begin
      select ruid into id from wylib.data_v where owner = userid and component = comp and name = nam;

      if dat is null then
        if found then
          delete from wylib.data_v where ruid = id;
        end if;
      elsif not found then
        insert into wylib.data_v (component, name, descr, owner, access, data) values (comp, nam, des, userid, 'read', dat) returning ruid into id;
      else
        update wylib.data_v set descr = des, data = dat where ruid = id;
      end if;
      return id;
    end;
$$;
create trigger base_addr_v_tr_ins instead of insert on base.addr_v for each row execute procedure base.addr_v_insfunc();
create trigger base_addr_v_tr_upd instead of update on base.addr_v for each row execute procedure base.addr_v_updfunc();
create trigger base_comm_v_tr_ins instead of insert on base.comm_v for each row execute procedure base.comm_v_insfunc();
create trigger base_comm_v_tr_upd instead of update on base.comm_v for each row execute procedure base.comm_v_updfunc();
create trigger base_file_v_tr_ins instead of insert on base.file_v for each row execute procedure base.file_v_insfunc();
create trigger base_file_v_tr_upd instead of update on base.file_v for each row execute procedure base.file_v_updfunc();
create view json.cert as select p.id
  , jsonb_strip_nulls(jsonb_build_object(
       'cid', p.peer_cid
     , 'agent', p.peer_agent
     , 'host', p.peer_host
     , 'port', p.peer_port
    )) as "chad"
  , p.ent_type	as "type"
  , p.peer_psig	as "public"
  , case when p.ent_type = 'o' then
      to_jsonb(p.ent_name)
    else
      jsonb_strip_nulls(jsonb_build_object('surname', p.ent_name, 'first', p.fir_name, 'middle', p.mid_name, 'prefer', p.pref_name))
    end		as "name"
  , (select array_agg(jsonb_strip_nulls(to_jsonb(d))) from (
      select media,address,comment from json.connect c
        where c.id = p.id and not prior and not private and main order by seq
    ) d) as "connect"
  , (select array_agg(jsonb_strip_nulls(to_jsonb(d))) from (
      select type,address,city,state,post,country,comment from json.place pl
        where not prior and not private and pl.id = p.id and type != 'birth' and main order by seq
    ) d) as "place"
  , (select array_agg(jsonb_strip_nulls(to_jsonb(d))) from (
      select media,digest,comment from json.file f
        where f.id = p.id and not private and main order by seq
    ) d) as "file"
  , jsonb_strip_nulls(jsonb_build_object(
      'state', jsonb_strip_nulls(jsonb_build_object('country', country, 'id', tax_id)),
      'birth', jsonb_strip_nulls(jsonb_build_object(
        'name', p.peer_named,
        'date', p.born_date,
        'place', (select jsonb_strip_nulls(to_jsonb(d)) from (
          select address,city,state,post,country,comment from json.place a
            where a.id = p.id and type = 'birth' and main limit 1
        ) as d )
      ))
  )) as "identity"
  , current_timestamp::timestamptz(3) as "date"
  
    from mychips.users_v p where not user_ent is null with cascaded check option;
create view json.users as select
  cid, agent, name, type, first, middle, prefer, begin, juris, taxid
  , (select array_agg(to_jsonb(d)) from (select type,address,city,state,post,country,main,comment,prior from json.place p where p.id = u.id order by seq) d) as place
  , (select array_agg(to_jsonb(d)) from (select media,address,main,comment,prior from json.connect c where c.id = u.id order by seq) d) as connect
    from json.user u;
create table mychips.chits (
chit_ent	text
  , chit_seq	int	      , foreign key (chit_ent, chit_seq) references mychips.tallies on update cascade on delete cascade
  , chit_idx	int	      , primary key (chit_ent, chit_seq, chit_idx)


  , chit_uuid	uuid		not null, constraint "!mychips.chits:CUU" unique (chit_ent,chit_seq,chit_uuid)
  , chit_type	text		not null default 'tran' constraint "!mychips.chits:BCT" check(chit_type in ('lift','tran','set'))
  , chit_date	timestamptz	not null default current_timestamp
  , issuer	tally_side	not null default 'foil'
  , units	bigint		constraint "!mychips.chits:CUN" check(units >= 0 and chit_type in ('lift','tran') or units isnull and chit_type = 'set')
  , reference	jsonb
  , memo	text
  , digest	bytea		
  , signature	text		constraint "!mychips.chits:GDS" check(status != 'good' or 
                                  (request isnull and not signature isnull) or 
                                  (request isnull and chit_type = 'lift'))


  , request	text	        constraint "mychips.chits.BRQ" check (request is null or request in ('pend','good','void'))
  , status	text		not null default 'draft' constraint "!mychips.chits:BST" check(status in ('draft','pend','good','void'))
  , chain_hash	bytea
  , chain_prev	bytea
  , chain_idx	int	      , unique(chit_ent, chit_seq, chain_idx)
  , chain_send	jsonb
  , lift_seq	int           , foreign key (chit_uuid, lift_seq) references mychips.lifts (lift_uuid, lift_seq) on update cascade on delete cascade
  , constraint "!mychips.chits:BLL" check (chit_type = 'lift' and not lift_seq isnull or chit_type != 'lift' and lift_seq isnull)
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create trigger mychips_contracts_v_tr_ins instead of insert on mychips.contracts_v for each row execute procedure mychips.contracts_v_insfunc();
create trigger mychips_contracts_v_tr_upd instead of update on mychips.contracts_v for each row execute procedure mychips.contracts_v_updfunc();
create function mychips.lift_chitcheck(lf mychips.lifts) returns mychips.lifts language plpgsql security definer as $$
    declare
      trec	record;
      uuid	uuid;
      stat	text = case when lf.status = 'good' then 'good' else 'pend' end;
      rows	int;
    begin


      foreach uuid in array lf.tallies loop

        for trec in select * from mychips.tallies where tally_uuid = uuid order by tally_type loop

          insert into mychips.chits (chit_ent, chit_seq, chit_type,
            chit_uuid, lift_seq, chit_date, status, units
          ) values (trec.tally_ent, trec.tally_seq, 'lift',
            lf.lift_uuid, lf.lift_seq, lf.lift_date, stat, -lf.units);

          get diagnostics rows = ROW_COUNT; if rows < 1 then
            raise exception '!mychips.lifts:CIF';
          end if;
        end loop;
      end loop;
      return lf;
    end;
$$;
create function mychips.lift_json(lf mychips.lifts) returns jsonb stable language sql as $$
    select jsonb_build_object(
       'lift',		lf.lift_uuid
     , 'date',		lf.lift_date
     , 'life',		lf.life
     , 'units',		lf.units
     , 'find',		lf.find
     , 'org',		lf.origin
     , 'ref',		lf.referee
    )
$$;
create function mychips.lifts_tf_notify() returns trigger language plpgsql security definer as $$
    declare
        dirty	boolean default false;
    begin
        if TG_OP = 'INSERT' and not new.request isnull then
            dirty = true;
        elsif not new.request isnull and new.request is distinct from old.request then
            dirty = true;
        end if;

        if dirty then perform mychips.lift_notify(new); end if;
        return new;
    end;
$$;
create function mychips.route_retry(new mychips.routes) returns boolean language plpgsql as $$
    begin


    return false;
    end;
$$;
create table mychips.route_tries (
rtry_rid	int		primary key references mychips.routes on update cascade on delete cascade
  , tries	int		not null default 1
  , last	timestamptz	not null default current_timestamp
);
create function mychips.ticket_login(info jsonb) returns base.token_v_ticket language plpgsql as $$
    declare
      uid	text;
    begin

      select into uid comm_ent from base.comm where comm_type = 'email'
        and not comm_inact and comm_spec = info->>'email';
      if found and info->>'reqType' = 'register' then
        return null;
      end if;
      select into uid id from mychips.users_v where ent_name = trim(info->>'ent_name')
          and (ent_type = 'o' and info->>'fir_name' isnull or fir_name = trim(info->>'fir_name'))
          and (born_date = (info->>'born_date')::date);
      if not found then 
        if info->>'reqType' != 'register' or info->>'tos' != 'true' or info->>'ent_type' isnull then
          return null; 
        end if;
        insert into mychips.users_v (
          ent_type, ent_name, fir_name, peer_cid, born_date,
          user_host, user_port,
          peer_agent, peer_host, peer_port
        ) values (
          info->>'ent_type',info->>'ent_name',info->>'fir_name',info->>'peer_cid',(info->>'born_date')::date,
          info->>'user_host', nullif(info->>'user_port','')::int,
          info->>'peer_agent', info->>'peer_host', nullif(info->>'peer_port','')::int
        )
            returning id into uid;
        insert into base.comm_v (comm_ent, comm_spec, comm_type)
          values (uid, info->>'email', 'email');
      end if;
      return mychips.ticket_login(uid);
    end;
$$;
create function mychips.token_tf_seq() returns trigger security definer language plpgsql as $$
    begin
      if new.token_ent isnull then			-- For creating my own tokens
         new.token_ent = base.curr_eid();
      end if;
      if new.token_seq is null then
        select into new.token_seq coalesce(max(token_seq),0)+1 from mychips.tokens where token_ent = new.token_ent;
      end if;
      if new.token is null then				-- If no token specified
        loop
          select into new.token md5(random()::text);
          if not exists (select token from mychips.tokens where token = new.token) then
            exit;
          end if;
        end loop;
      end if;
      return new;
    end;
$$;
create trigger mychips_users_v_tr_ins instead of insert on mychips.users_v for each row execute procedure mychips.users_v_insfunc();
create trigger mychips_users_v_tr_upd instead of update on mychips.users_v for each row execute procedure mychips.users_v_updfunc();
create trigger wylib_data_v_tr_del instead of delete on wylib.data_v for each row execute procedure wylib.data_v_tf_del();
create trigger wylib_data_v_tr_ins instead of insert on wylib.data_v for each row execute procedure wylib.data_v_tf_ins();
create trigger wylib_data_v_tr_upd instead of update on wylib.data_v for each row execute procedure wylib.data_v_tf_upd();
create function mychips.chain_notify_agent(ch mychips.chits) returns boolean language plpgsql security definer as $$
    declare
        channel	text	= 'mychips_agent';
        jrec	jsonb;
        trec	record;
        cmd	text = 'upd';
    begin
        select into trec tally_uuid,hold_chad,hold_agent,part_chad from mychips.tallies_v where tally_ent = ch.chit_ent and tally_seq = ch.chit_seq;
        if not trec.hold_agent is null then
            channel = 'ma_' || trec.hold_agent;
        end if;

        jrec = jsonb_build_object(
          'target',	'chit',
          'action',	'chain',
          'sub',	cmd,
          'to',		trec.part_chad,
          'from',	trec.hold_chad,
          'object',	ch.chain_send || jsonb_build_object(
            'tally',	trec.tally_uuid,
            'uuid',	ch.chit_uuid
          )
        );
raise notice 'Chain notice:% Cmd:% E:% Cid:%', channel, cmd, ch.chit_ent, trec.part_chad->>'cid';
        perform pg_notify(channel, jrec::text);
        return true;
    end;
$$;
create function mychips.chain_process(msg jsonb, recipe jsonb) returns text language plpgsql as $$
    declare
      cid	text	= msg->'to'->>'cid';
      agent	text	= msg->'to'->>'agent';
      cmd	text	= msg->>'sub';
      obj	jsonb	= msg->'object';
      index	int4;
      crec	record;
      trec	record;
      jrec	jsonb;
      qrec	record;
    begin
raise notice 'Chain process cid:% msg:% recipe:%', cid, msg, recipe;
      select into trec tally_ent, tally_seq, tally_type, chain_conf from mychips.tallies_v where hold_cid = cid and tally_uuid = (obj->>'tally')::uuid;
      if not found then return null; end if;
raise notice 'Chain T:%-% conf:% cid:%', trec.tally_ent, trec.tally_seq, trec.chain_conf, cid;


      if recipe::boolean then	-- No chits sent == ACK
        update mychips.chits set chain_send = null
          where chit_ent = trec.tally_ent and chit_seq = trec.tally_seq and chit_uuid = (obj->>'uuid')::uuid;



      elsif cmd = 'upd' and (obj->>'chits') isnull then	-- No chits sent == ACK
        index = obj->>'index';
        select into crec chit_ent, chit_seq, chit_idx, chain_hash, chain_idx, state from mychips.chits_v where chit_ent = trec.tally_ent and chit_seq = trec.tally_seq and chain_idx = index;
        if not found then return null; end if;
raise notice 'Chain C:%-% A:%', crec.chit_ent, crec.chit_seq, cmd;
raise notice 'Chain ack:%-% ix:%-%', crec.chain_hash, obj->>'chain', crec.chain_idx, index;
        if crec.chain_hash = (obj->>'chain')::bytea and crec.chain_idx = index then
          update mychips.tallies set chain_conf = index where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
        end if;


      elsif cmd = 'upd' and (obj->>'chits') notnull then
raise notice 'Chain upd:%', obj->'chits';
        for qrec in select * from (	-- Compare the unconfirmed chits we have on stock end
            select * from mychips.chits
              where chit_ent = trec.tally_ent and chit_seq = trec.tally_seq
                and status = 'good' and chain_idx > trec.chain_conf
          ) c full join (		-- To the linked ones the foil has sent us
            select jsonb_array_elements(obj->'chits') as j
          ) jc on (jc.j->>'digest')::bytea = c.digest
          order by jc.j->'index'
        loop

raise notice '  chit upd X:% D:% J:%', qrec.chain_idx, qrec.digest, qrec.j;
          if qrec.j isnull then		-- The foil is missing a valid chit we have
raise notice 'SEND->FOIL';
            continue;
          end if;

          index = (qrec.j->'index')::int;
          update mychips.chits set chain_idx = null where chit_ent = trec.tally_ent and chit_seq = trec.tally_seq and chain_idx = index;
          if qrec.chit_ent isnull then		-- We are missing this chit which the foil has
raise notice 'ADD @:%', index;
            insert into mychips.chits (
              chit_ent,chit_seq,chit_uuid,chit_date,status,
              signature,issuer,units,reference,memo,chain_idx
            ) values (
              trec.tally_ent, trec.tally_seq, (qrec.j->>'uuid')::uuid,
              (qrec.j->>'date')::timestamptz, 'good',
              qrec.j->>'signed', (qrec.j->>'by')::tally_side, (qrec.j->>'units')::bigint, 
              qrec.j->'ref', qrec.j->>'memo', index
            );

          else		-- Otherwise, we just need to apply the foil's version of the chain index
raise notice 'INDEX %->%', qrec.chain_idx, index;
            update mychips.chits set
              chain_idx = index, chain_prev = null, status = 'reproc'
              where chit_ent = qrec.chit_ent and chit_seq = qrec.chit_seq and chit_idx = qrec.chit_idx;
          end if;

        end loop;
      end if;

      return 'OK';
    end;
$$;
create function mychips.chit_cstate(ch mychips.chits, ta mychips.tallies) returns text immutable language sql as $$
    select case
      when ch.chain_idx isnull then			'Unlinked'
      when ch.chain_idx <= ta.chain_conf then		'Linked'
      when ch.chain_send notnull then			'Notify'
      when ch.request = 'good' then			'Linking'
      else						'Pending' end
$$;
create function mychips.chit_json_c(ch mychips.chits, ta mychips.tallies) returns jsonb stable language sql as $$
    select jsonb_strip_nulls(jsonb_build_object(
      'tally',		ta.tally_uuid,
      'by',		ch.issuer,
      'type',		ch.chit_type,
      'uuid',		ch.chit_uuid,
      'date',		ch.chit_date,
      'units',		ch.units,
      'ref',		ch.reference,
      'memo',		ch.memo
    ))
$$;
create index mychips_chits_x_chit_date on mychips.chits (chit_date);
create index mychips_chits_x_chit_type on mychips.chits (chit_type);
create index mychips_chits_x_chit_uuid on mychips.chits (chit_uuid);
create index mychips_chits_x_status on mychips.chits (status);
create table mychips.chit_tries (
ctry_ent	text	      , primary key (ctry_ent, ctry_seq, ctry_idx)
  , ctry_seq	int
  , ctry_idx	int	      , foreign key (ctry_ent, ctry_seq, ctry_idx) references mychips.chits on update cascade on delete cascade
  , tries	int		not null default 1
  , last	timestamptz	not null default current_timestamp
);
create function mychips.lifts_tf_ai() returns trigger language plpgsql security definer as $$
    begin
        if new.request = 'relay' or new.request = 'found'
          or (new.lift_type = 'in' and new.status = 'good') then
            return mychips.lift_chitcheck(new);
        end if;
        return new;
    end;
$$;
create function mychips.lifts_tf_bu() returns trigger language plpgsql security definer as $$
    declare
      lrec	record;
    begin
      if old.status in ('good','void') then return null; end if;
      
      if not ((new.lift_uuid is not distinct from old.lift_uuid) and (new.find is not distinct from old.find) and (new.origin is not distinct from old.origin) and (new.referee is not distinct from old.referee) and (new.units is not distinct from old.units) and (new.life is not distinct from old.life) and (new.lift_date is not distinct from old.lift_date)) then
        new.digest = mychips.j2h(mychips.lift_json(new));
      end if;

      if new.status != old.status then
        if new.status = 'seek' then
          return mychips.lift_chitcheck(new);
        elsif new.status in ('good','void') then
          update mychips.chits set status = new.status where chit_uuid = new.lift_uuid and lift_seq = new.lift_seq;
        end if;
      end if;
      return new;
    end;
$$;
create trigger mychips_lifts_tr_notice after insert or update on mychips.lifts for each row execute procedure mychips.lifts_tf_notify();
create function mychips.tally_notices() returns int language plpgsql as $$
    declare
        trec		mychips.tallies;
        crec		mychips.chits;
        didem		int = 0;
        min_min		int = coalesce(base.parm_int('agents','min_time'), 60);
        min_time	interval = (min_min::text || ' minutes')::interval;
    begin
        for trec in select * from mychips.tallies ta	-- tokens stale by peer_min_time
          join mychips.tally_tries tr on tr.ttry_ent = ta.tally_ent and tr.ttry_seq = ta.tally_seq
          where ta.request is not null and (current_timestamp - tr.last) >= min_time loop
            perform mychips.tally_notify_agent(trec);
            didem = didem + 1;
        end loop;

        for crec in select * from mychips.chits ch
          join mychips.chit_tries ct on ct.ctry_ent = ch.chit_ent and ct.ctry_seq = ch.chit_seq and ct.ctry_idx = ch.chit_idx
          where ch.request is not null and (current_timestamp - ct.last) >= min_time loop
            perform mychips.chit_notify(crec);
            didem = didem + 1;
        end loop;
        return didem;
    end;
$$;
create function mychips.ticket_process(ticket jsonb, uname text = session_user) returns boolean language plpgsql as $$
    declare
      trec	record;
    begin
      if session_user != 'admin' then	-- admin can spoof a user (for testing)
        uname = session_user;
      end if;
    
      select into trec id, peer_agent from mychips.users_v where username = uname;
      if found and not trec.peer_agent isnull then
        ticket = ticket				-- Build message for agent to act on
          || '{"target":"tally","action":"ticket"}' 
          || jsonb_build_object('cert', mychips.user_cert(trec.id));


        perform pg_notify('ma_' || trec.peer_agent, ticket::text);
        return true;
      end if;
      return false;
    end;
$$;
create view mychips.tokens_v as select
    t.token_ent, t.token_seq, t.reuse, t.expires, t.tally_seq, t.token, t.used, t.crt_by, t.mod_by, t.crt_date, t.mod_date
  , u.peer_cid, u.peer_agent, u.std_name
  , t.expires <= current_timestamp as "expired"
  , t.expires > current_timestamp and used is null and a.status = 'draft' as "valid"
  , jsonb_build_object(
       'cid', u.peer_cid
     , 'agent', u.peer_agent
     , 'host', u.peer_host
     , 'port', u.peer_port
    ) as "chad"
      
    from	mychips.tokens		t
    join	mychips.users_v		u	on u.user_ent = t.token_ent
    join	mychips.tallies	a	on a.tally_ent = t.token_ent and a.tally_seq = t.tally_seq

    ;
    ;
create trigger mychips_token_tr_seq before insert on mychips.tokens for each row execute procedure mychips.token_tf_seq();
create function mychips.user_cert(uid text) returns jsonb language sql as $$
    select to_jsonb(s) as cert from (
      select date,chad,type,name,public,connect,place,identity from json.cert where id = uid
    ) s
$$;
create function mychips.chit_json_h(ch mychips.chits, ta mychips.tallies) returns jsonb stable language sql as $$
    select mychips.chit_json_c(ch, ta) || jsonb_strip_nulls(jsonb_build_object(
      'index',		ch.chain_idx,
      'prior',		ch.chain_prev,
      'signed',		ch.signature
    ))
$$;
create function mychips.chit_json_r(ch mychips.chits, ta mychips.tallies) returns jsonb stable language sql as $$
    select mychips.chit_json_c(ch, ta) || jsonb_strip_nulls(jsonb_build_object(
      'digest',		ch.digest,
      'signed',		ch.signature,
      'index',		ch.chain_idx,
      'chain',		ch.chain_hash
    ))
$$;
create trigger mychips_lifts_tr_ai after insert on mychips.lifts for each row execute procedure mychips.lifts_tf_ai();
create trigger mychips_lifts_tr_bu before update on mychips.lifts for each row execute procedure mychips.lifts_tf_bu();
create function mychips.tally_certs(ta mychips.tallies) returns mychips.tallies language plpgsql security definer as $$
    declare
      hchad jsonb; pchad jsonb; c jsonb;
    begin

      hchad = ta.hold_cert->'chad';
      pchad = ta.part_cert->'chad';
      ta.hold_cid   = hchad->>'cid';
      ta.hold_agent = hchad->>'agent';
      ta.part_cid   = pchad->>'cid';
      ta.part_agent = pchad->>'agent';

      foreach c in array array[ hchad, pchad ] loop
        if (c->>'agent') notnull and not exists (select agent from mychips.agents where agent = c->>'agent') then
          insert into mychips.agents (agent, agent_host, agent_port) values (c->>'agent', c->>'host', (c->'port')::int);
        end if;
      end loop;


      select into ta.part_ent user_ent from mychips.users_v where peer_cid = ta.part_cid and peer_agent = ta.part_agent;
      return ta;
    end;
$$;
create function mychips.tokens_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.tokens_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.tokens (token_ent,token_seq,reuse,expires,tally_seq,token,crt_by,mod_by,crt_date,mod_date) values (new.token_ent,new.token_seq,trec.reuse,trec.expires,trec.tally_seq,trec.token,session_user,session_user,current_timestamp,current_timestamp) returning token_ent,token_seq into new.token_ent, new.token_seq;
    select into new * from mychips.tokens_v where token_ent = new.token_ent and token_seq = new.token_seq;
    return new;
  end;
$$;
create view mychips.tokens_v_me as select 
    t.*
    from	mychips.tokens_v t
    where	t.token_ent = base.user_id(session_user);
select wm.create_role('tally_1');
grant select on table mychips.tokens_v_me to tally_1;
select wm.create_role('tally_2');
grant select on table mychips.tokens_v_me to tally_2;
grant insert on table mychips.tokens_v_me to tally_2;
grant update on table mychips.tokens_v_me to tally_2;
select wm.create_role('tally_3');
grant delete on table mychips.tokens_v_me to tally_3;
create function mychips.tokens_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.tokens set reuse = new.reuse,expires = new.expires,mod_by = session_user,mod_date = current_timestamp where token_ent = old.token_ent and token_seq = old.token_seq returning token_ent,token_seq into new.token_ent, new.token_seq;
    select into new * from mychips.tokens_v where token_ent = new.token_ent and token_seq = new.token_seq;
    return new;
  end;
$$;
create function mychips.token_valid(tok text, cert jsonb = null) returns boolean language plpgsql as $$
    declare
      orec	record;
      trec	record;
    begin
      select into orec valid,token,reuse,token_ent,token_seq,tally_seq from mychips.tokens_v where token = tok;

      if cert isnull then			-- Checking only
        return found and orec.valid;
      elsif not found or not orec.valid then
        return false;
      end if;

      if orec.reuse then	-- Create a new tally from the template
        insert into mychips.tallies (
          tally_ent, tally_uuid, tally_type, version, comment, contract, hold_cert, hold_terms, part_cert, status
        ) select
          tally_ent, uuid_generate_v4(), tally_type, version, comment, contract, hold_cert, hold_terms, cert, 'draft'
        from mychips.tallies returning tally_ent, tally_seq into trec;
        perform mychips.tally_notify_user(trec.tally_ent, trec.tally_seq);
      else			-- one-time token, use template AS our new tally, invalidate token
        update mychips.tokens set used = current_timestamp where token_ent = orec.token_ent and token_seq = orec.token_seq;
        update mychips.tallies set part_cert = cert, status = 'draft' where tally_ent = orec.token_ent and tally_seq = orec.tally_seq;
        perform mychips.tally_notify_user(orec.token_ent, orec.tally_seq);
      end if;
      return true;
    end;
$$;
create view mychips.chits_v as select 
    ch.chit_ent, ch.chit_seq, ch.chit_idx, ch.request, ch.signature, ch.units, ch.reference, ch.memo, ch.chit_uuid, ch.chit_type, ch.issuer, ch.crt_by, ch.mod_by, ch.crt_date, ch.mod_date, ch.chit_date, ch.chain_send, ch.chain_idx, ch.chain_hash, ch.chain_prev, ch.lift_seq, ch.status, ch.digest
  , te.hold_cid
  , te.part_cid
  , te.tally_type
  , te.tally_uuid
  , te.chain_conf

  , case when ch.issuer = te.tally_type then -(ch.units) else (ch.units) end							as net
  , case when ch.status = 'good' then case when ch.issuer = te.tally_type then -(ch.units) else (ch.units) end else 0 end	as net_g
  , case when ch.status = 'void' then 0 else case when ch.issuer = te.tally_type then -(ch.units) else (ch.units) end end	as net_p

  , mychips.chit_cstate(ch, te)					as cstate
  , mychips.chit_state(ch.issuer != te.tally_type, ch.status, ch.request)	as state
  , mychips.chit_state(ch.issuer != te.tally_type, ch.status, ch.request) = any(array['L.pend']) as action
  , mychips.chit_json_c(ch, te)					as json_core
  , mychips.chit_json_r(ch, te)					as json
  , mychips.j2h(mychips.chit_json_h(ch, te))			as hash_v
  , mychips.j2h(mychips.chit_json_h(ch, te)) = coalesce(ch.chain_hash,'') as clean

    from	mychips.chits	ch
    join	mychips.tallies	te on te.tally_ent = ch.chit_ent and te.tally_seq = ch.chit_seq;

    ;
    ;
select wm.create_role('chit_1');
grant select on table mychips.chits_v to chit_1;
select wm.create_role('chit_2');
grant insert on table mychips.chits_v to chit_2;
grant update on table mychips.chits_v to chit_2;
select wm.create_role('chit_3');
grant delete on table mychips.chits_v to chit_3;
create function mychips.tallies_tf_bu() returns trigger language plpgsql security definer as $$
    begin
      if not new.request isnull then		-- check for legal state transition requests
        if not (
          new.request in ('void','draft','offer') and old.status in ('void', 'draft', 'offer') or
          new.request = 'open' and old.status = 'offer'
        ) then raise exception '!mychips.tallies:IST % %', old.status, new.request;
        end if;
        if new.request = 'offer' then		-- Our user is re-drafting
          new.part_sig = null;
          new.status = 'draft';
        end if;
      end if;
      
      if new.hold_cert isnull then
        new.hold_cert = mychips.user_cert(new.tally_ent);
      end if;
      if new.hold_cert is distinct from old.hold_cert or new.part_cert is distinct from old.part_cert then
        new = mychips.tally_certs(new);
      end if;

      if new.status != old.status then			-- Check for valid state transitions
        if new.status = 'open' and old.status = 'offer' then
          new.digest = mychips.j2h(mychips.tally_json(new));
          new.hold_sets = new.hold_terms;
          new.part_sets = new.part_terms;
        elsif new.status in ('draft','void','offer') and old.status in ('void','draft','offer') then
          null;
        elsif new.status = 'close' and old.status = 'open' then
          null;
        else
          raise exception '!mychips.tallies:IST % %', old.status, new.status;
        end if;
      end if;
      new.bound = greatest(new.target, new.bound);
      return new;
    end;
$$;
create function mychips.tallies_tf_seq() returns trigger language plpgsql security definer as $$
    begin
        if new.tally_ent is null then
          new.tally_ent = base.user_id(session_user);
        end if;
        if new.tally_seq is null then
          update mychips.users set _last_tally = greatest(
              coalesce(_last_tally, 0) + 1,
              (select coalesce(max(tally_seq),0)+1 from mychips.tallies where tally_ent = new.tally_ent)
            ) where user_ent = new.tally_ent
              returning _last_tally into new.tally_seq;
          if not found then new.tally_seq = 1; end if;

        end if;
        if new.tally_uuid is null then
          new.tally_uuid = uuid_generate_v4();
        end if;

        if new.hold_cert is null then
          new.hold_cert = mychips.user_cert(new.tally_ent);
        end if;
        new = mychips.tally_certs(new);
        if new.status = 'open' then	-- Should only happen in simulations
          new.digest = mychips.j2h(mychips.tally_json(new));
        end if;
        new.bound = greatest(new.target, new.bound);
        return new;
    end;
$$;
create trigger mychips_tokens_v_tr_ins instead of insert on mychips.tokens_v for each row execute procedure mychips.tokens_v_insfunc();
create trigger mychips_tokens_v_tr_upd instead of update on mychips.tokens_v for each row execute procedure mychips.tokens_v_updfunc();
select wm.create_role('mychips', '{"user_2","contract_1","tally_2","chit_2","mychips_1"}'); select base.pop_role('mychips');
create function mychips.chain_consense(ch mychips.chits, ta mychips.tallies) returns mychips.chits language plpgsql as $$
    declare
      crec	record;
      propHash	bytea = ch.chain_hash;
      prevHash	bytea;
      nextIdx	int;
      propIdx	int = ch.chain_idx;
      ratchet	boolean = false;
      jrec	jsonb;
    begin
      select into crec * from mychips.chits	-- Find the current end of chain
        where chit_ent = ch.chit_ent and chit_seq = ch.chit_seq
          and chain_idx notnull order by chain_idx desc limit 1;
raise notice 'Cons T:%-%-% Conf:% Iss:% Units:% Ex:%', ta.tally_ent,ta.tally_seq,ta.tally_type,ta.chain_conf,ch.issuer,ch.units,crec.chain_idx;

      if found then				-- Already have a chain
        nextIdx = greatest(crec.chain_idx + 1, 1);
        prevHash = crec.chain_hash;
      else					-- No chits in chain yet
        nextIdx = 1;
        prevHash = ta.digest;
      end if;
raise notice 'Cons CH: Ix:% nextIdx:% prev:%', ch.chain_idx, nextIdx, prevHash;

      if ch.chain_idx isnull then		-- Use given index
        ch.chain_idx = nextIdx;
      end if;

      if ta.tally_type = 'foil' then		-- Holding the foil; we are in charge of chit order
        ch.chain_prev = prevHash;
        ch.chain_idx = nextIdx;
        ch.chain_hash = mychips.j2h(mychips.chit_json_h(ch, ta));

        if ch.issuer != ta.tally_type then	-- chit issued by stock

          if ch.chain_hash = propHash then	-- did the stock compute the endhash correctly?
raise notice 'Ack with Stock hash:%', ch.chain_hash;
            ch.chain_send = jsonb_build_object(	-- We are in a trigger handler, update send flag
              'index',	nextIdx,
              'chain',	ch.chain_hash
            );

          else					-- stock's hash doesn't look right
raise notice 'Notify Stock of chits %-% hash:%', propIdx, nextIdx, ch.chain_hash;
            select into jrec jsonb_agg(json) from (	-- List sequence of chits the stock evidently has wrong
              select json from mychips.chits_v where chain_idx between propIdx and nextIdx
                and chit_ent = ch.chit_ent and chit_seq = ch.chit_seq order by chain_idx
            ) s;
            ch.chain_send = jsonb_build_object(	-- We are in a trigger handler, update send flag
              'chits',	jrec || mychips.chit_json_r(ch,ta)	-- Include the present chit
            );
          end if;
        end if;
        ratchet = true;
raise notice 'Chain FOIL: idx:% hash:% prv:%', ch.chain_idx, ch.chain_hash, ch.chain_prev;

      else		-- we hold the stock, must conform to foil
        ch.chain_prev = prevHash;
        ch.chain_hash = mychips.j2h(mychips.chit_json_h(ch, ta));

        if ch.issuer != ta.tally_type then	-- If foil issued this chit
raise notice 'Got foil chit conf:% idx:% hash:%', ta.chain_conf, ch.chain_idx, propHash;
          if ch.chain_hash != propHash then	-- Does our hash disagree with what the foil sent?
raise notice 'Request chits from foil since:% hash:%', ta.chain_conf, ch.chain_hash;
            ch.chain_prev = null;
            ch.chain_idx = null;
          else					-- We agree with foil's hash
            ratchet = true;
          end if;
        else					-- We (stock) issued this chit
raise notice 'Assume chit placement at X:% Conf:%', ch.chain_idx, ta.chain_conf;
        end if;
raise notice 'Chain STOCK: idx:% hash:% prv:%', ch.chain_idx, ch.chain_hash, ch.chain_prev;














        
      end if;


      if ratchet then				-- Move chain_conf forward
        update mychips.tallies set chain_conf = ch.chain_idx where tally_ent = ch.chit_ent and tally_seq = ch.chit_seq;
      end if;
      
      return ch;
    end;
$$;
create function mychips.chit_goodcheck(ch mychips.chits) returns mychips.chits language plpgsql security definer as $$
    declare
      trec	mychips.tallies;
      settings	jsonb;
    begin

      if ch.chit_type != 'lift' and ch.signature isnull then	-- Fixme: check actual signature validity?
        raise exception '!mychips.chits:MIS %-%', ch.chit_ent, ch.chit_seq;
      end if;
      
      if ch.chain_prev notnull then return ch; end if;

      select into trec * from mychips.tallies where tally_ent = ch.chit_ent and tally_seq = ch.chit_seq;
      if not found or trec.digest isnull then		-- Can we find the valid tally the chit belongs to?
        raise exception '!mychips.chits:LIT %-%-%', trec.tally_ent, trec.tally_seq, trec.tally_type;
        return null;
      end if;

      if ch.chit_type = 'set' then			-- Apply tally settings
        settings = ch.reference;
        update mychips.tallies set
          hold_sets = hold_sets || case when ch.issuer = trec.tally_type then settings else '{}' end,
          part_sets = part_sets || case when ch.issuer = trec.tally_type then '{}' else settings end,
          target = coalesce((settings->>'target')::bigint, target),
          bound  = coalesce((settings->>'bound')::bigint,  bound),
          reward = coalesce((settings->>'reward')::float,  reward), 
          clutch = coalesce((settings->>'clutch')::float,  clutch), 
          status = case when status = 'open' and (settings->'close')::boolean then 'close' else status end	-- Enact any close request
        where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
      end if;

      ch.digest = mychips.j2h(mychips.chit_json_c(ch, trec));
      return mychips.chain_consense(ch, trec);
    end;
$$;
create function mychips.chit_process(msg jsonb, recipe jsonb) returns text language plpgsql as $$
    declare
      cid	text	= msg->'to'->>'cid';
      agent	text	= msg->'to'->>'agent';
      obj	jsonb	= msg->'object';
      uuid	uuid	= obj->>'uuid';
      curState	text;
      qstrg	text;
      trec	record;
      crec	record;
      erec	record;
      jrec	jsonb;
    begin
      if msg->>'action' = 'chain' then		-- Chaining has its own handler
        return mychips.chain_process(msg,recipe);
      end if;

raise notice 'Chit top cid:% obj:%', cid, obj;
      select into trec tally_ent, tally_seq, tally_type from mychips.tallies_v where hold_cid = cid and tally_uuid = (obj->>'tally')::uuid;
      if not found then return null; end if;

      select into crec chit_ent, chit_seq, chit_idx, state from mychips.chits_v where chit_ent = trec.tally_ent and chit_uuid = uuid;
      curState = crec.state;

      if not found then
        curState = 'null';
      end if;

      if not (jsonb_build_array(curState) <@ (recipe->'context')) then	--Not in any applicable state (listed in our recipe context)

        return curState;
      end if;

      if recipe ? 'upsert' then

        if curState = 'null' then			-- Need to do insert
          insert into mychips.chits (
            chit_ent,chit_seq,chit_uuid,chit_type,chit_date,status,
            signature,issuer,units,reference,memo,chain_hash,chain_idx		--,chain_prev
          ) values (
            trec.tally_ent, trec.tally_seq, uuid, obj->>'type', (obj->>'date')::timestamptz,
            coalesce(recipe->'upsert'->>'status','pend'),
            obj->>'signed', (obj->>'by')::tally_side, (obj->>'units')::bigint, 
            obj->'ref', obj->>'memo', (obj->>'chain')::bytea,(obj->>'index')::int	--, (obj->>'prior')::bytea
          ) returning chit_ent, chit_seq, chit_idx, chain_hash into crec;

        else						-- Chit already exists, do update
          update mychips.chits set signature = obj->>'signed', 
            issuer = (obj->>'by')::tally_side, units = (obj->>'units')::bigint,
            status = coalesce(recipe->'upsert'->>'status','pend'),
            reference = obj->'ref', memo = obj->>'memo', chain_hash = (obj->>'chain')::bytea, chain_idx = (obj->>'index')::int,
            request = null, mod_date = current_timestamp, mod_by = session_user
            where chit_ent = crec.chit_ent and chit_seq = crec.chit_seq and chit_idx = crec.chit_idx;

          delete from mychips.chit_tries where ctry_ent = crec.chit_ent and ctry_seq = crec.chit_seq and ctry_idx = crec.chit_idx;
        end if;
      end if;

      if recipe ? 'update' then			-- There's an update key in the recipe
        qstrg = mychips.state_updater(recipe, 'mychips.chits', '{status, signature}');

        execute qstrg || ' chit_ent = $1 and chit_seq = $2 and chit_idx = $3' using crec.chit_ent, crec.chit_seq, crec.chit_idx;
        delete from mychips.chit_tries where ctry_ent = crec.chit_ent and ctry_seq = crec.chit_seq and ctry_idx = crec.chit_idx;
      end if;

      select into crec chit_ent,chit_seq,chit_idx,chit_uuid,state,action,json from mychips.chits_v where chit_ent = crec.chit_ent and chit_seq = crec.chit_seq and chit_idx = crec.chit_idx;
      if crec.action or (crec.state is distinct from curState) then	-- Also notify if changed state
        jrec = jsonb_build_object(
          'target',	'chit',
          'entity',	crec.chit_ent,
          'sequence',	crec.chit_seq,
          'index',	crec.chit_idx,
          'state',	crec.state,
          'object',	crec.json
        );

        perform pg_notify('mu_' || crec.chit_ent, jrec::text);

        perform pg_notify('mychips_user', crec.json::text);
      end if;
      return crec.state;

    end;
$$;
create function mychips.chits_tf_cache() returns trigger language plpgsql security definer as $$
    declare
      trec	record;

    begin

      if TG_OP = 'DELETE' then trec = old; else trec = new; end if;





      update mychips.tallies set 	-- mod_date = current_timestamp, mod_by = session_user, 
        net_c = coalesce(cs.sum_g,0), net_pc = coalesce(cs.sum_p,0) from (
          select sum(net_g) as sum_g, sum(net_p) as sum_p
          from mychips.chits_v where chit_ent = trec.chit_ent and chit_seq = trec.chit_seq
        ) as cs
          where	tally_ent = trec.chit_ent and tally_seq = trec.chit_seq;

      return null;
    end;
$$;
create function mychips.chits_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.chits_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.chits (chit_ent,chit_seq,request,signature,units,reference,memo,chit_uuid,chit_type,issuer,crt_by,mod_by,crt_date,mod_date) values (new.chit_ent,new.chit_seq,trec.request,trec.signature,trec.units,trec.reference,trec.memo,trec.chit_uuid,trec.chit_type,trec.issuer,session_user,session_user,current_timestamp,current_timestamp) returning chit_ent,chit_seq,chit_idx into new.chit_ent, new.chit_seq, new.chit_idx;
    select into new * from mychips.chits_v where chit_ent = new.chit_ent and chit_seq = new.chit_seq and chit_idx = new.chit_idx;
    return new;
  end;
$$;
create function mychips.chits_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.chits set request = new.request,signature = new.signature,units = new.units,reference = new.reference,memo = new.memo,mod_by = session_user,mod_date = current_timestamp where chit_ent = old.chit_ent and chit_seq = old.chit_seq and chit_idx = old.chit_idx returning chit_ent,chit_seq,chit_idx into new.chit_ent, new.chit_seq, new.chit_idx;
    select into new * from mychips.chits_v where chit_ent = new.chit_ent and chit_seq = new.chit_seq and chit_idx = new.chit_idx;
    return new;
  end;
$$;
create trigger mychips_tallies_tr_bu before update on mychips.tallies for each row execute procedure mychips.tallies_tf_bu();
create trigger mychips_tallies_tr_seq before insert on mychips.tallies for each row execute procedure mychips.tallies_tf_seq();
create view mychips.tallies_v as select 
    te.tally_ent, te.tally_type, te.comment, te.contract, te.hold_terms, te.part_terms, te.target, te.reward, te.clutch, te.bound, te.part_sig, te.hold_sig, te.request, te.tally_uuid, te.version, te.part_ent, te.hold_cert, te.part_cert, te.tally_seq, te.status, te.digest, te.net_pc, te.net_c, te.tally_date, te.hold_cid, te.hold_agent, te.part_cid, te.part_agent, te.hold_sets, te.part_sets, te.chain_conf, te.crt_by, te.mod_by, te.crt_date, te.mod_date
  , jsonb_build_object('cid', te.hold_cid) || ua.json as hold_chad
  , ua.agent_host			as hold_host
  , ua.agent_port			as hold_port



  , te.part_cid ||':'|| pa.agent	as part_addr
  , jsonb_build_object('cid', te.part_cid) || pa.json as part_chad
  , pa.agent_host			as part_host
  , pa.agent_port			as part_port

  
  , not te.part_ent is null						as inside
  , mychips.tally_state(status,request,hold_sig,part_sig)		as state
  , mychips.tally_state(status,request,hold_sig,part_sig) = any(array['P.offer','draft']) as action
  , te.status = 'open' or (te.status = 'close' and net_pc != 0)		as liftable

  , coalesce(cg.chits, 0)				as chits
  , coalesce(cg.chits, 0) + coalesce(ce.chits, 0)	as chits_p

  , coalesce(cg.net, 0)					as net
  , coalesce(cg.net, 0) + coalesce(ce.net, 0)		as net_p
  
  , greatest(cg.latest, te.mod_date)			as latest
  
  , mychips.tally_json(te) as json_core
  , mychips.tally_json(te) || jsonb_build_object(
      'sign',		json_build_object(
        'digest',	te.digest,
        'stock',	case when te.tally_type = 'stock' then te.hold_sig else te.part_sig end,
        'foil',		case when te.tally_type = 'stock' then te.part_sig else te.hold_sig end
      )
    )		as json
  , mychips.j2h(mychips.tally_json(te)) as digest_v
  , mychips.j2h(mychips.tally_json(te)) = coalesce(te.digest,'') as clean
  , jsonb_build_object(
      'target',		te.target,
      'reward',		te.reward,
      'clutch',		te.clutch,
      'bound',		te.bound
    )		as policy
  , cc.digest		as ack_hash

    from	mychips.tallies	te
    left join	mychips.agents_v ua on ua.agent = te.hold_agent
    left join	mychips.agents_v pa on pa.agent = te.part_agent
    left join	(select chit_ent, chit_seq,
         sum(net) as net, count(chit_idx) as chits, max(mod_date) as latest
         from mychips.chits_v where status = 'good' and chit_type != 'set' group by 1,2
       ) cg on cg.chit_ent = te.tally_ent and cg.chit_seq = te.tally_seq
    left join	(select chit_ent, chit_seq,
         sum(net) as net, count(chit_idx) as chits, max(mod_date) as latest
         from mychips.chits_v where status = 'pend' and chit_type != 'set' group by 1,2
       ) ce on ce.chit_ent = te.tally_ent and ce.chit_seq = te.tally_seq
    left join	(select chit_ent,chit_seq,chain_idx,digest from mychips.chits_v where status = 'good'
       ) cc on cc.chit_ent = te.tally_ent and cc.chit_seq = te.tally_seq
         and cc.chain_idx = te.chain_conf;

    ;
create view json.tally as select
    te.tally_ent	as "id"
  , te.tally_seq	as "seq"
  , te.version		as "version"
  , te.tally_uuid	as "uuid"
  , te.tally_date	as "date"
  , te.tally_type	as "type"
  , te.comment		as "comment"
  , te.contract		as "agree"
  , te.hold_cert	as "holder"
  , te.hold_terms	as "hterms"
  , te.part_cert	as "partner"
  , te.part_terms	as "pterms"
    from mychips.tallies te;
create function mychips.chit_notify_agent(chit mychips.chits) returns boolean language plpgsql security definer as $$
    declare
        channel	text	= 'mychips_agent';
        jrec	jsonb;
        trec	record;
        rrec	record;
    begin
        select into trec tally_uuid,hold_chad,hold_agent,part_chad from mychips.tallies_v where tally_ent = chit.chit_ent and tally_seq = chit.chit_seq;
        if not trec.hold_agent is null then
            channel = 'ma_' || trec.hold_agent;
        end if;
        insert into mychips.chit_tries (ctry_ent, ctry_seq, ctry_idx) values (chit.chit_ent, chit.chit_seq, chit.chit_idx)
          on conflict (ctry_ent,ctry_seq,ctry_idx) do update set tries = mychips.chit_tries.tries + 1, last = current_timestamp
            returning * into rrec;
        
        jrec = jsonb_build_object(
          'target',	'chit',
          'action',	chit.request,
          'try',	rrec.tries,
          'last',	rrec.last,
          'to',		trec.part_chad,
          'from',	trec.hold_chad,
          'object',	(select json from mychips.chits_v where chit_ent = chit.chit_ent and chit_seq = chit.chit_seq and chit_idx = chit.chit_idx)
        );

        perform pg_notify(channel, jrec::text);
        return true;
    end;
$$;
create function mychips.chits_tf_bu() returns trigger language plpgsql security definer as $$
    begin
      if new.status != old.status then			-- Check for valid state transitions
        if not (
          new.status in ('draft','pend') and old.status in ('draft','pend') or
          new.status = 'pend' and old.status = 'void' or
          new.status in ('void','good') and old.status = 'pend' or
          new.status = 'reproc'
        ) then raise exception '!mychips.chits:IST % %', old.status, new.status;
        end if;
      end if;

      if new.request = 'pend' then		-- User is drafting/re-drafting
        new.status = 'draft';
      elsif new.request = 'good' then		-- User is sending good pledge
        new.status = 'pend';
        return mychips.chit_goodcheck(new);
      elsif new.status = 'good' and old.status != 'good' then	-- Received good chit
        return mychips.chit_goodcheck(new);
      elsif new.status = 'reproc' then		-- Need to reorder this chit in the chain
        new.status = 'good';
        return mychips.chit_goodcheck(new);
      end if;
      return new;
    end;
$$;
create function mychips.chits_tf_seq() returns trigger language plpgsql security definer as $$
    begin
      if new.chit_idx is null then			-- update should lock the mychips.tallies row until transaction completes
        update mychips.tallies set _last_chit = greatest(
            coalesce(_last_chit,0) + 1,
            (select coalesce(max(chit_idx),0)+1 from mychips.chits where chit_ent = new.chit_ent and chit_seq = new.chit_seq)
          ) where tally_ent = new.chit_ent and tally_seq = new.chit_seq
            returning _last_chit into new.chit_idx;
        if not found then new.chit_idx = 1; end if;

      end if;
      if new.units < 0 then			-- Interpret negative units as meaning stock-issued
        new.units = -new.units;
        new.issuer = 'stock';
      end if;

      if new.request = 'pend' then		-- User is drafting
        new.status = 'draft';
      elsif new.request = 'good' then		-- User is sending good pledge
        new.status = 'pend';
        return mychips.chit_goodcheck(new);

      elsif new.status = 'good' then		-- A signed chit from peer can come in marked as good
        return mychips.chit_goodcheck(new);
      end if;
      return new;
    end;
$$;
create trigger mychips_chits_tr_cache after insert or update or delete on mychips.chits for each row execute procedure mychips.chits_tf_cache();
create view mychips.chits_v_chains as with recursive chit_chain(ent, seq, chain_idx, chain_prev, chain_hash, chain_conf, prev_ok, hash_ok, length, uuids, cycle) as (
    select	t.tally_ent, t.tally_seq, 0::int, null::bytea, t.digest, t.chain_conf, true, 
      t.digest_v = t.digest, 0::int, array[t.tally_uuid], false
    from	mychips.tallies_v t
  union all
    select c.chit_ent					as ent
      , c.chit_seq					as seq
      , c.chain_idx					as chain_idx
      , c.chain_prev					as chain_prev
      , c.chain_hash					as chain_hash
      , cc.chain_conf					as chain_conf
      , cc.prev_ok and (c.chain_prev = cc.chain_hash)	as prev_ok
      , cc.hash_ok and (c.hash_v = c.chain_hash)	as hash_ok
      , cc.length + 1					as length
      , cc.uuids || c.chit_uuid				as uuids
      , c.chit_uuid = any(cc.uuids)			as cycle
    from	chit_chain	cc
    join	mychips.chits_v	c on c.chit_ent = cc.ent and c.chit_seq = cc.seq and c.chain_idx = cc.chain_idx + 1
  ) select
    ccc.ent
  , ccc.seq
  , ccc.chain_idx
  , ccc.chain_prev
  , ccc.chain_hash
  , ccc.chain_conf
  , ccc.prev_ok
  , ccc.hash_ok
  , ccc.prev_ok and ccc.hash_ok as ok
  , ccc.chain_idx = cm.max as last
  , ccc.length
  , ccc.uuids
  from chit_chain ccc		-- where ccc.length > 1
  join (
    select chit_ent,chit_seq,max(chain_idx) as max from mychips.chits group by 1,2
  ) cm on cm.chit_ent = ccc.ent and cm.chit_seq = ccc.seq;
create trigger mychips_chits_v_tr_ins instead of insert on mychips.chits_v for each row execute procedure mychips.chits_v_insfunc();
create trigger mychips_chits_v_tr_upd instead of update on mychips.chits_v for each row execute procedure mychips.chits_v_updfunc();
create function mychips.lifts_tf_bi() returns trigger language plpgsql security definer as $$
    declare
      trec	record;
    begin
        if new.lift_uuid isnull then
          new.lift_uuid = uuid_generate_v4();
          new.lift_seq = 0;
        elsif new.lift_seq isnull then		-- This is not safe for concurrent insertions
          select into new.lift_seq coalesce(max(lift_seq)+1,0) from mychips.lifts where lift_uuid = new.lift_uuid;
        end if;

        if new.status = 'draft' and new.request = 'seek' then	-- General consistency check
          if new.life isnull then
            new.life = base.parm('lifts', 'life', '2 minutes'::text)::interval;
          end if;
        end if;

        new.digest = mychips.j2h(mychips.lift_json(new));
        return new;
    end;
$$;
create view mychips.lifts_v as select 
    lf.lift_uuid, lf.request, lf.find, lf.origin, lf.referee, lf.status, lf.signature, lf.lift_date, lf.lift_type, lf.tallies, lf.units, lf.life, lf.circuit, lf.lift_seq, lf.digest
  , mychips.lift_state(lf.status, lf.request)			as state

  , mychips.lift_json(lf)					as json_core
  , mychips.lift_json(lf) || jsonb_build_object(
      'digest',		lf.digest
    )								as json
  , mychips.j2h(mychips.lift_json(lf))				as digest_v
  , mychips.j2h(mychips.lift_json(lf)) = coalesce(lf.digest,'') as clean
  , lf.lift_date + lf.life					as expires
  , lf.lift_date + lf.life - crt_date				as remains

    from	mychips.lifts	lf

    ;
    ;
select wm.create_role('lift_1');
grant select on table mychips.lifts_v to lift_1;
select wm.create_role('lift_2');
grant insert on table mychips.lifts_v to lift_2;
grant update on table mychips.lifts_v to lift_2;
select wm.create_role('lift_3');
grant delete on table mychips.lifts_v to lift_3;
create view mychips.routes_v as select 
    ro.rid, ro.status, ro.min, ro.max, ro.margin, ro.reward, ro.via_ent, ro.via_tseq, ro.dst_cid, ro.dst_agent, ro.req_ent, ro.req_tseq, ro.step, ro.lift_count, ro.lift_date, ro.good_date
  , it.hold_cid		as via_cid
  , it.hold_agent	as via_agent
  , it.hold_chad	as via_chad
  , it.tally_uuid	as via_tally
  , it.part_cid		as vip_cid		-- Route via this partner peer
  , it.part_agent	as vip_agent
  , it.part_chad	as vip_chad

  , qt.hold_cid		as req_cid		-- Our user/owner of downstream request tally
  , qt.hold_agent	as req_agent
  , qt.hold_chad	as req_chad
  , qt.tally_uuid	as req_tally
  , qt.part_cid		as rpt_cid		-- Foreign partner request came through
  , qt.part_agent	as rpt_agent
  , qt.part_chad	as rpt_chad

  , jsonb_build_object('cid', ro.dst_cid, 'agent', ro.dst_agent)	as dst_chad
  , ro.req_tseq isnull or not qt.part_ent isnull			as native
  , rt.tries		as tries
  , rt.last		as last
  , greatest(ro.good_date, ro.lift_date) + pl.life		as expires
  , current_timestamp > greatest(ro.good_date, ro.lift_date) + pl.life					as expired
  , mychips.route_state(ro.status, current_timestamp > greatest(ro.good_date, ro.lift_date) + pl.life)	as state

  , jsonb_build_object(
      'min'   ,	ro.min,		'max'   , ro.max
    , 'margin',	ro.margin,	'reward', ro.reward
   )									as lading
  , jsonb_build_object(				-- For upstream query packet
       'step',		ro.step
     , 'tally',		it.tally_uuid
     , 'find' ,	jsonb_build_object(
         'cid', 	ro.dst_cid
       , 'agent',	ro.dst_agent
       )
    )			as json

    from	mychips.routes		ro
    join	mychips.users_v		ie on ie.user_ent = ro.via_ent
    join	mychips.tallies_v	it on it.tally_ent = ro.via_ent and it.tally_seq = ro.via_tseq
    left join	mychips.tallies_v	qt on qt.tally_ent = ro.req_ent and qt.tally_seq = ro.req_tseq
    left join	mychips.route_tries	rt on rt.rtry_rid = ro.rid
    join	(select coalesce(value, '1 hour')::interval as life
                 from base.parm_v where module = 'routes' and parm = 'life') pl on true;

    ;
    ;
create function mychips.tallies_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.tallies_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.tallies (tally_ent,tally_type,comment,contract,hold_terms,part_terms,target,reward,clutch,bound,part_sig,hold_sig,request,tally_uuid,version,part_ent,hold_cert,part_cert,crt_by,mod_by,crt_date,mod_date) values (new.tally_ent,trec.tally_type,trec.comment,trec.contract,trec.hold_terms,trec.part_terms,trec.target,trec.reward,trec.clutch,trec.bound,trec.part_sig,trec.hold_sig,trec.request,trec.tally_uuid,trec.version,trec.part_ent,trec.hold_cert,trec.part_cert,session_user,session_user,current_timestamp,current_timestamp) returning tally_ent,tally_seq into new.tally_ent, new.tally_seq;
    select into new * from mychips.tallies_v where tally_ent = new.tally_ent and tally_seq = new.tally_seq;
    return new;
  end;
$$;
create view mychips.tallies_v_me as select 
    t.*
    from	mychips.tallies_v t
    where	t.tally_ent = base.user_id(session_user);
grant select on table mychips.tallies_v_me to tally_1;
grant select on table mychips.tallies_v_me to tally_2;
grant insert on table mychips.tallies_v_me to tally_2;
grant update on table mychips.tallies_v_me to tally_2;
grant delete on table mychips.tallies_v_me to tally_3;
create view mychips.tallies_v_net as with
  t_loc as (select tally_ent, tally_seq, tally_type, tally_uuid, part_ent, target, reward, bound, clutch, net_pc, part_addr
    from mychips.tallies_v where liftable and not part_ent isnull
  ),
  t_for as (select tally_ent, tally_seq, tally_type, tally_uuid, part_ent, target, reward, bound, clutch, net_pc, part_addr
    from mychips.tallies_v where liftable and part_ent isnull
  )
  select 			-- Internal tallies with both stock and foil
    t.tally_ent, t.tally_seq, t.tally_type, t.part_ent, t.tally_uuid as uuid
  , t.part_ent					as inp
  , t.tally_ent					as out
  , t.target, t.bound, t.reward
  , coalesce(p.clutch, 0)			as margin
  , t.net_pc
  , greatest(t.target - t.net_pc,0)		as min
  , t.bound - t.net_pc				as max
  , case when t.tally_type = 'foil' then 'lift' else 'drop' end as type
  , case when t.tally_type = 'foil' then -1 else 1 end as sign
  , case when t.part_ent isnull then t.part_addr else null end	as part
  , false					as inv
  , t.net_pc < t.bound				as canlift
    from	t_loc as t
    join 	t_loc as p on t.tally_uuid = p.tally_uuid and t.tally_ent != p.tally_ent

  union select 			-- Tallies with foreign peers, lifting toward us
    t.tally_ent, t.tally_seq, t.tally_type, t.part_ent, t.tally_uuid as uuid
  , t.part_ent					as inp
  , t.tally_ent					as out
  , t.target, t.bound, t.reward
  , 0						as margin
  , t.net_pc
  , greatest(t.target - t.net_pc,0)		as min
  , t.bound - t.net_pc				as max
  , case when t.tally_type = 'foil' then 'lift' else 'drop' end as type
  , case when t.tally_type = 'foil' then -1 else 1 end as sign
  , case when t.part_ent isnull then t.part_addr else null end	as part
  , false					as inv
  , t.net_pc < t.bound				as canlift
    from	t_for as t

  union select 			-- Tallies with foreign peers, lifting toward them
    t.tally_ent, t.tally_seq, t.tally_type, t.part_ent, t.tally_uuid as uuid
  , t.tally_ent					as inp
  , t.part_ent					as out
  , 0 as target, 0 as bound
  , 0 as reward, 0 as margin				-- Assume zero costs from other side
  , -t.net_pc as net_pc
  , null					as min	-- Nulls because other side of 

  , null					as max

  , case when t.tally_type = 'foil' then 'drop' else 'lift' end as type
  , case when t.tally_type = 'foil' then 1 else -1 end as sign
  , case when t.part_ent isnull then t.part_addr else null end	as part
  , true					as inv
  , true					as canlift	-- Let the other side limit lifts

    from	t_for as t;
create view mychips.tallies_v_sum as select 
    tally_ent
  , count(tally_seq)						as tallies
  , sum(net)							as net
  , array_agg(part_ent)						as part_ents
  , array_agg(part_cid)						as part_cids
  , array_agg(part_agent)					as part_agents
  , array_agg(tally_uuid)					as uuids
  , array_agg(tally_seq)					as seqs
  , array_agg(tally_type)					as types
  , array_agg(state)						as states
  , array_agg(net)						as nets
  , array_agg(inside)						as insides

  , array_agg(target)						as targets
  , array_agg(reward)						as rewards
  , array_agg(bound)						as bounds
  , array_agg(clutch)						as clutchs
  , array_agg(policy)						as policies

  , sum(net) filter (where tally_type = 'stock')		as stock_net
  , sum(net) filter (where tally_type = 'foil')			as foil_net

  , count(nullif(tally_type, 'foil'))::int4			as stocks
  , count(nullif(tally_type, 'stock'))::int4			as foils
  , array_agg(part_ent) filter (where tally_type = 'stock')	as clients
  , array_agg(part_ent) filter (where tally_type = 'foil')	as vendors
  , array_agg(part_cid) filter (where tally_type = 'stock')	as client_cids
  , array_agg(part_agent) filter (where tally_type = 'stock')	as client_agents
  , array_agg(part_cid) filter (where tally_type = 'foil')	as vendor_cids
  , array_agg(part_agent) filter (where tally_type = 'foil')	as vendor_agents
  , array_agg(tally_uuid) filter (where tally_type = 'stock')	as stock_uuids
  , array_agg(tally_uuid) filter (where tally_type = 'foil')	as foil_uuids
  , array_agg(tally_seq) filter (where tally_type = 'stock')	as stock_seqs
  , array_agg(tally_seq) filter (where tally_type = 'foil')	as foil_seqs
  , array_agg(net) filter (where tally_type = 'stock')		as stock_nets
  , array_agg(net) filter (where tally_type = 'foil')		as foil_nets

  , max(latest)							as latest
  , jsonb_agg(jsonb_build_object(
      'ent',	tally_ent
    , 'seq',	tally_seq
    , 'type',	tally_type
    , 'uuid',	tally_uuid
    , 'net',	net
    , 'part',	part_cid || ':' || part_agent
  ))								as json
  from (select * from mychips.tallies_v order by net) t
  group by 1;
create function mychips.tallies_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    if old.status = 'draft' then
      update mychips.tallies set tally_type = new.tally_type,comment = new.comment,contract = new.contract,hold_terms = new.hold_terms,part_terms = new.part_terms,target = new.target,reward = new.reward,clutch = new.clutch,bound = new.bound,part_sig = new.part_sig,hold_sig = new.hold_sig,request = new.request,crt_by = session_user,mod_by = session_user,crt_date = current_timestamp,mod_date = current_timestamp where tally_ent = old.tally_ent and tally_seq = old.tally_seq
    returning tally_ent,tally_seq into new.tally_ent, new.tally_seq;
    else
      update mychips.tallies set request = new.request,crt_by = session_user,mod_by = session_user,crt_date = current_timestamp,mod_date = current_timestamp where tally_ent = old.tally_ent and tally_seq = old.tally_seq
    returning tally_ent,tally_seq into new.tally_ent, new.tally_seq;
    end if;
    select into new * from mychips.tallies_v where tally_ent = new.tally_ent and tally_seq = new.tally_seq;
    return new;
  end;
$$;
create function mychips.tally_notify_agent(tally mychips.tallies) returns boolean language plpgsql security definer as $$
    declare
        jrec	jsonb;
        trec	record;
        rrec	record;
        channel	text = 'mychips_agent';
    begin				-- Determine next action

        select into trec hold_agent,hold_chad,part_chad,json from mychips.tallies_v where tally_ent = tally.tally_ent and tally_seq = tally.tally_seq;
        if not trec.hold_agent is null then
            channel = 'ma_' || trec.hold_agent;
        end if;

        insert into mychips.tally_tries (ttry_ent, ttry_seq) values (tally.tally_ent, tally.tally_seq)
          on conflict (ttry_ent,ttry_seq) do update set tries = mychips.tally_tries.tries + 1, last = current_timestamp
            returning * into rrec;


        jrec = jsonb_build_object(
          'target',	'tally',
          'action',	tally.request,
          'try',	rrec.tries,
          'last',	rrec.last,
          'to',		trec.part_chad,
          'from',	trec.hold_chad,
          'object',	trec.json
        );

        perform pg_notify(channel, jrec::text);
        return true;
    end;
$$;
create function mychips.tally_notify_user(ent text, seq int, oldstate text = 'open') returns record language plpgsql as $$
    declare
      trec	record;
      jrec	jsonb;
    begin
      select into trec tally_ent,tally_seq,state,action,json from mychips.tallies_v where tally_ent = ent and tally_seq = seq;
      if trec.action or (trec.state is distinct from oldState) then	-- Also notify if changed state

        jrec = jsonb_build_object(
          'target',	'tally',
          'entity',	trec.tally_ent,
          'sequence',	trec.tally_seq,
          'state',	trec.state,
          'object',	trec.json
        );
        perform pg_notify('mu_' || trec.tally_ent, jrec::text);
        perform pg_notify('mychips_user', jrec::text);
      end if;
      return trec;
    end;
$$;
create function mychips.tally_process(msg jsonb, recipe jsonb) returns text language plpgsql as $$
    declare
      cid	text = msg->'to'->>'cid';
      agent	text = msg->'to'->>'agent';
      obj	jsonb = msg->'object';
      uuid	uuid = obj->>'uuid';
      hold	jsonb = obj->'stock';
      part	jsonb = obj->'foil';
      curState	text;
      qstrg	text;
      uid	text;
      trec	record;
      jrec	jsonb;
      acted	boolean = false;
      tallyType tally_side = 'stock';
      notType	tally_side = 'foil';
    begin

      select into trec tally_ent, tally_seq, state from mychips.tallies_v where hold_cid = cid and tally_uuid = uuid;
        

      if not found then			-- No existing tally
        curState = 'null';
        select into uid id from mychips.users_v where peer_cid = cid and peer_agent = agent;
        if not found then return null; end if;
      else
        curState = trec.state;
        uid = trec.tally_ent;
      end if;
      if not (jsonb_build_array(curState) <@ (recipe->'context')) then	--Not in any applicable state (listed in our recipe context)

        return curState;
      end if;

      if recipe ? 'upsert' then		-- If inserting/updating from object

        if part->'cert'->'chad'->>'cid' = cid and part->'cert'->'chad'->>'agent' = agent then
          tallyType = 'foil';
          notType = 'stock';
          hold	= obj->'foil';
          part	= obj->'stock';
        elsif hold->'cert'->'chad'->>'cid' != cid or hold->'cert'->'chad'->>'agent' != agent then
          return null;
        end if;


        if curState = 'null' then			-- Will need to do insert
          insert into mychips.tallies (
            tally_ent,tally_uuid,tally_type,tally_date,version,contract,status,comment,
            hold_sig,part_sig,hold_terms,part_terms,hold_cert,part_cert
          ) values (
            uid, uuid, tallyType, (obj->>'date')::timestamptz, (obj->>'version')::int, 
            obj->'agree', coalesce(recipe->'upsert'->>'status','offer'),
            obj->>'note', obj->'sign'->>(tallyType::text), obj->'sign'->>(notType::text), 
            hold->'terms', part->'terms', hold->'cert', part->'cert'
          ) returning tally_ent, tally_seq into trec;
        else						-- Tally already exists, do an update
          update mychips.tallies set request = null, mod_date = current_timestamp, mod_by = session_user,
            status = coalesce(recipe->'upsert'->>'status','offer'),
            version = (obj->>'version')::int, contract = obj->'agree', comment = obj->>'note',
            hold_sig = obj->'sign'->>(tallyType::text), part_sig = obj->'sign'->>(notType::text),
            hold_terms = hold->'terms', part_terms = part->'terms',
            hold_cert = hold->'cert', part_cert = part->'cert'
          where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
        end if;
        acted = true;
      end if;

      if recipe ? 'update' then			-- There's an update key in the recipe
        qstrg = mychips.state_updater(recipe, 'mychips.tallies', '{status, part_cert, part_sig}');

        execute qstrg || ' tally_ent = $1 and tally_seq = $2' using trec.tally_ent, trec.tally_seq;
        acted = true;
      end if;

      if not acted then		-- Don't proceed if we didn't do anything
        return null;
      end if; 


      delete from mychips.tally_tries where ttry_ent = trec.tally_ent and ttry_seq = trec.tally_seq;


      trec = mychips.tally_notify_user(trec.tally_ent, trec.tally_seq, curState);
      return trec.state;
    end;
$$;
create view mychips.users_v_tallies as with
  t as (select
    tally_ent, tally_seq, tally_type, tally_uuid, net, inside, part_cid, part_agent, latest
    from mychips.tallies_v order by net
  ),
  s as (select tally_ent
    , count(tally_seq)					as count
    , sum(net)						as net
    , sum(net) filter (where net >= 0)			as asset
    , count(net) filter (where net >= 0)		as assets
    , sum(net) filter (where net < 0)			as liab
    , count(net) filter (where net < 0)			as liabs
    , max(latest)					as latest

    , jsonb_agg(jsonb_build_object(
        'ent',		tally_ent
      , 'seq',		tally_seq
      , 'type',		tally_type
      , 'uuid',		tally_uuid
      , 'net',		net
      , 'inside',	inside
      , 'part',		part_cid || ':' || part_agent
      ))							as tallies
    from t group by 1
  )
  select u.*
    , coalesce(s.count, 0)			as count
    , coalesce(s.net, 0)			as net
    , coalesce(s.asset, 0)			as asset
    , coalesce(s.assets, 0)			as assets
    , coalesce(s.liab, 0)			as liab
    , coalesce(s.liabs, 0)			as liabs
    , greatest(s.latest, u.mod_date)		as latest
    , coalesce(s.tallies, '[]'::jsonb)		as tallies
  
    from	mychips.users_v u
    left join	s on s.tally_ent = u.user_ent;
create function json.import(data jsonb, target text default null, keys jsonb default null) returns record language plpgsql as $$
    declare
      tmpObject		jsonb;
      tableName		text;
      newRecord		record;
      fieldArray	text[];
      fieldList		text;
      primKeyList	text;
      cmd		text;
      tmpKey		text;
    begin

      if target isnull then						-- better be able to figure out target from key(s)
        for tableName in select jsonb_object_keys(data) loop		-- For each record in toplevel object
          tmpObject = data->tableName;
          return json.import(tmpObject, tablename, keys);
        end loop;
      
      elsif jsonb_typeof(data) = 'array' then
        for tmpObject in select jsonb_array_elements(data) loop		-- Recursively call for each array element
          newRecord = json.import(tmpObject, target, keys);
        end loop;
        return newRecord;
        
      elsif jsonb_typeof(data) != 'object' then				-- Better be left with a single object
        return null;
      end if;

      select array_to_string(pkey,',') into primKeyList from wm.table_data where td_sch = 'json' and td_tab = target;
      if not found or primKeyList isnull then	-- Skip any tables we don't know how to import

        return null;
      end if;
      

      for tmpKey in select jsonb_object_keys(keys) loop		-- For any primary key values passed in from above
        data = jsonb_set(data, array[tmpkey], keys->tmpkey);

      end loop;

      select array_agg(cdt_col), string_agg(quote_ident(cdt_col),',') into fieldArray, fieldList from wm.column_data where cdt_sch = 'json' and cdt_tab = target;

      cmd = 'insert into json.' || quote_ident(target) || ' (' || fieldList || ') select ' || fieldList || ' from jsonb_populate_record(NULL::json.' || quote_ident(target) || ', $1) returning ' || primKeyList;

      execute cmd into newRecord using data;


      for tmpKey in select jsonb_object_keys(data) loop		-- Find any nested sub-objects that need to be inserted
        if not (tmpKey = any(fieldArray)) then

          perform json.import(data->tmpKey, tmpKey, to_jsonb(newRecord));
        end if;
      end loop;
      

      return newRecord;
    end;
$$;
create function mychips.chits_tf_notify() returns trigger language plpgsql security definer as $$
    declare
        dirty	boolean default false;
    begin
        if TG_OP = 'INSERT' and not new.request isnull then
            dirty = true;
        elsif (not new.request isnull) and (new.request is distinct from old.request) then
            dirty = true;
        end if;
raise notice 'Chit update:% send:%', dirty, new.chain_send;
        if dirty then				-- Communicate chit message
          perform mychips.chit_notify_agent(new);
        end if;

        if new.chain_send notnull then		-- Communicate consensus message
          perform mychips.chain_notify_agent(new);
        end if;
        return new;
    end;
$$;
create trigger mychips_chits_tr_bu before update on mychips.chits for each row execute procedure mychips.chits_tf_bu();
create trigger mychips_chits_tr_seq before insert on mychips.chits for each row execute procedure mychips.chits_tf_seq();
create view mychips.chits_v_me as select 
    c.*
    from	mychips.chits_v c
    join	mychips.tallies_v_me t on c.chit_ent = t.tally_ent and c.chit_seq = t.tally_seq;
grant select on table mychips.chits_v_me to chit_1;
grant select on table mychips.chits_v_me to chit_2;
grant insert on table mychips.chits_v_me to chit_2;
grant update on table mychips.chits_v_me to chit_2;
grant delete on table mychips.chits_v_me to chit_3;
create function mychips.lift_process(msg jsonb, recipe jsonb) returns jsonb language plpgsql as $$
    declare
        obj		jsonb		= msg->'object';
        seq		int		= msg->'sequence';
        uuid		uuid		= obj->>'lift';
        units		bigint		= obj->>'units';


        find		jsonb		= obj->'find';
        req		text		= 'relay';
        lrec		record;
        qrec		record;
        curState	text;
        qstrg		text;
        remain		interval;
    begin
raise notice 'Lift process uuid:% seq:% recipe:%', uuid, seq, recipe;
      if recipe ? 'query' then			-- If there a query key in the recipe object

        remain = (obj->>'date')::timestamptz + (obj->>'life')::interval - current_timestamp;

        if remain < base.parm('lifts', 'minlife', '1 second'::text)::interval then
          return null;
        end if;
        
raise notice '  find:% @%', find->>'cid', msg->>'tally';


        select into qrec uuids,foro from mychips.tallies_v_paths where


          bot_uuid = (msg->>'tally')::uuid and fori and
          out_cid = find->>'cid' and out_agent = find->>'agent' and
          min >= units order by edges desc limit 1;
raise notice 'Search path: %:% found:% for:%', find->>'cid', find->>'agent', found, qrec.foro;


        if not found then		-- Next, try searching upstream routes:
          select into qrec uuids, true as foro from mychips.routes_v_paths where


            bot_uuid = (msg->>'tally')::uuid and fori and
            dst_cid = find->>'cid' and dst_agent = find->>'agent' and
            path_min >= units order by route_min desc, edges desc limit 1;
raise notice 'Search route: %:% %', find->>'cid', find->>'agent', found;
          if not found then return null; end if;
        end if;

        if not qrec.foro then req = 'found'; end if;
        insert into mychips.lifts_v (
          request, units, lift_type, lift_uuid, tallies, lift_date, find, origin, referee, life
        ) values (
          req, units, 'rel', uuid, qrec.uuids, (obj->>'date')::timestamptz,
          find, obj->'org', obj->'ref', (obj->>'life')::interval
        ) returning request, state into lrec;
raise notice ' returning: %', lrec.state;
        return to_jsonb(lrec.state);
      end if;

      if uuid notnull and seq notnull then	-- Explicit lift referenced for update
raise notice ' find by seq:%-%', uuid, seq;
        select into lrec lift_uuid,lift_seq,state from mychips.lifts_v
          where lift_uuid = uuid and lift_seq = seq;
      else				-- Find lift by base tally
raise notice ' find % by bot/top tally:%', uuid, msg->>'tally';
        select into lrec lift_uuid,lift_seq,state from mychips.lifts_v_dist
          where lift_uuid = uuid and 
            (bot_tally = (msg->>'tally')::uuid or top_tally = (msg->>'tally')::uuid);
      end if;
      if not found then return null; end if;

      if recipe ? 'loop' then		-- Form complete loopback path to originator for circular lift
        find = recipe->'loop';
raise notice ' loop:%-%', find, msg->'tally';
        select into qrec uuids from mychips.tallies_v_paths
          where bot_uuid = (msg->>'tally')::uuid and fori
            and out_cid = find->>'cid' and out_agent = find->>'agent' and foro
            and min >= units order by edges desc limit 1;
raise notice '  loop path: %:% found:%', find->>'cid', find->>'agent', found;
        if not found then return to_jsonb(curState); end if;
        update mychips.lifts set tallies = qrec.uuids		-- Add all tallies back to originator
          where lift_uuid = lrec.lift_uuid and lift_seq = lrec.lift_seq;
      end if;
      
      if recipe ? 'update' then
        if found then curState = lrec.state; else curState = 'null'; end if;
raise notice 'Lift state:%', curState;

        if not (jsonb_build_array(curState) <@ (recipe->'context')) then	--Not in any applicable state (listed in our recipe context)
raise notice 'Lift Z:% C:%', jsonb_build_array(curState), recipe->'context';
          return to_jsonb(curState);
        end if;

        qstrg = mychips.state_updater(recipe, 'mychips.lifts_v', 
          '{status, request, origin, referee, find, lift_uuid, tallies, signature}', 
          case when recipe->'update' ? 'request' then '{}'::text[] else '{"request = null"}' end
        );
raise notice 'SQL:% % %', qstrg, lrec.lift_uuid, lrec.lift_seq;
        execute qstrg || ' lift_uuid = $1 and lift_seq = $2 
          returning lift_uuid, lift_seq, state' into lrec using lrec.lift_uuid, lrec.lift_seq;
        return to_jsonb(lrec.state);
      end if;

    return null;
    end;
$$;
create trigger mychips_lifts_tr_bi before insert on mychips.lifts for each row execute procedure mychips.lifts_tf_bi();
create view mychips.lifts_v_dist as select lf.*
  , tt.hold_chad					as top_chad
  , tt.part_chad					as out_chad
  , tt.tally_uuid					as top_tally
  , bt.hold_chad					as bot_chad
  , bt.part_chad					as inp_chad
  , bt.tally_uuid					as bot_tally



  , coalesce(lf.origin, jsonb_build_object(
      'agent',	bt.hold_agent		-- Or use system agent here?
    , 'host',	bt.hold_host
    , 'port',	bt.hold_port
    , 'plan',	jsonb_build_object(
        'cid',		bt.hold_cid
      , 'agent',	bt.hold_agent)
    ))							as origin_v

  , coalesce(lf.find, jsonb_build_object(
      'cid',	bt.part_cid
    , 'agent',	bt.part_agent
    ))							as find_v

  , coalesce(lf.referee, jsonb_build_object(
      'agent',	bt.hold_agent
    , 'host',	bt.hold_host
    , 'port',	bt.hold_port
    ))							as referee_v

    from mychips.lifts_v	lf
    left join	mychips.tallies_v	tt on tt.part_ent isnull and
    		tt.tally_uuid = lf.tallies[array_upper(lf.tallies,1)]
    left join	mychips.tallies_v	bt on bt.part_ent isnull and
    		bt.tally_uuid = lf.tallies[array_lower(lf.tallies,1)];
create function mychips.lifts_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.lifts_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.lifts (lift_uuid,request,find,origin,referee,status,signature,lift_date,lift_type,tallies,units,life,circuit,crt_by,mod_by,crt_date,mod_date) values (new.lift_uuid,trec.request,trec.find,trec.origin,trec.referee,trec.status,trec.signature,trec.lift_date,trec.lift_type,trec.tallies,trec.units,trec.life,trec.circuit,session_user,session_user,current_timestamp,current_timestamp) returning lift_uuid,lift_seq into new.lift_uuid, new.lift_seq;
    select into new * from mychips.lifts_v where lift_uuid = new.lift_uuid and lift_seq = new.lift_seq;
    return new;
  end;
$$;
create function mychips.lifts_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.lifts set lift_uuid = new.lift_uuid,request = new.request,find = new.find,origin = new.origin,referee = new.referee,status = new.status,signature = new.signature,mod_by = session_user,mod_date = current_timestamp where lift_uuid = old.lift_uuid and lift_seq = old.lift_seq returning lift_uuid,lift_seq into new.lift_uuid, new.lift_seq;
    select into new * from mychips.lifts_v where lift_uuid = new.lift_uuid and lift_seq = new.lift_seq;
    return new;
  end;
$$;
create function mychips.route_notify(route mychips.routes) returns void language plpgsql security definer as $$
    declare
        jrec	jsonb;
        orec	record;
        prec	record;
        rrec	record;
        channel	text = 'mychips_agent';
    begin
        if route.status = 'pend' then			-- pend: no notification needed
          return;				
        end if;


        insert into mychips.route_tries (rtry_rid) values (route.rid)
          on conflict (rtry_rid) do update set tries = mychips.route_tries.tries + 1, last = current_timestamp
            returning * into rrec;

        jrec = jsonb_build_object('target', 'route'
          , 'action'	, route.status
          , 'try'	, rrec.tries
          , 'last'	, rrec.last
        );


        select into orec via_chad, via_agent, vip_chad, native, step, json,
          req_ent, req_chad, req_agent, req_tally, rpt_chad, dst_chad, lading
            from mychips.routes_v where rid = route.rid;

        if route.status = 'draft' then			-- draft: request upstream query
          if not orec.via_agent isnull then channel = 'ma_' || orec.via_agent; end if;
          jrec = jrec || jsonb_build_object(
              'to'	, orec.vip_chad
            , 'from'	, orec.via_chad
            , 'object'	, orec.json
          );

        elsif route.status in ('good','none') then	-- good,none: notify someone


          if (orec.native) then				-- Notify requesting local user
            jrec = jsonb_build_object('target','route'
              , 'action',	route.status
              , 'object', jsonb_build_object('route',	route.rid
                , 'find',	orec.dst_chad
                , 'lading',	case when route.status = 'good' then orec.lading else null end
              )
            );

            perform pg_notify('mu_' || route.req_ent, jrec::text);
            return;

          elsif route.status = 'good' then		-- Notify downstream site (only of good's)



            select into prec rid, jsonb_build_object('min',min,'max',max,'margin',margin,'reward',reward) as lading
              from	mychips.routes_v_paths
              where	rid = route.rid and bot = req_ent and bot_tseq = req_tseq
              order by	margin, min desc, max desc limit 1;


            channel = 'ma_' || orec.req_agent;
            jrec = jrec || jsonb_build_object(
                'to'	,	orec.rpt_chad
              , 'from'	,	orec.req_chad
              , 'object',  jsonb_build_object(
                  'tally',	orec.req_tally
                , 'lading',	coalesce(prec.lading, orec.lading)	-- Full path lading if available
              )
            );
          end if;
        end if;


        perform pg_notify(channel, jrec::text);
    end;
$$;
create function mychips.route_pop(qrec record, currStep int = 0) returns jsonb language plpgsql security definer as $$
    declare
      lading	jsonb;
      forward	int = 0;
    begin

      if (qrec.status isnull) then

        insert into mychips.routes (via_ent, via_tseq, dst_cid, dst_agent, step, req_ent, req_tseq)
          values (qrec.top, qrec.top_tseq, qrec.find_cid, qrec.find_agent, currStep, qrec.bot, 
            case when currStep <= 0 then null else qrec.bot_tseq end		-- Native or externally requested query
          );
        forward = 1;

      elsif (qrec.expired) then
        update mychips.routes set status = 'draft', step = currStep where rid = qrec.rid;
        forward = 1;

      elsif (qrec.status = 'good' and lading isnull) then
        lading = jsonb_build_object(
          'min', qrec.min, 'max', qrec.max,'margin', qrec.margin, 'reward', qrec.reward);
      end if;

      return jsonb_build_object(
        'forward',	forward,
        'lading',	lading
      );
    end;
$$;
create function mychips.routes_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.routes_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.routes (status,min,max,margin,reward,via_ent,via_tseq,dst_cid,dst_agent,req_ent,req_tseq) values (trec.status,trec.min,trec.max,trec.margin,trec.reward,trec.via_ent,trec.via_tseq,trec.dst_cid,trec.dst_agent,trec.req_ent,trec.req_tseq) returning rid into new.rid;
    select into new * from mychips.routes_v where rid = new.rid;
    return new;
  end;
$$;
create function mychips.routes_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.routes set status = new.status,min = new.min,max = new.max,margin = new.margin,reward = new.reward where rid = old.rid returning rid into new.rid;
    select into new * from mychips.routes_v where rid = new.rid;
    return new;
  end;
$$;
create trigger mychips_tallies_tr_upd instead of update on mychips.tallies_v for each row execute procedure mychips.tallies_v_updfunc();
create view mychips.tallies_v_paths as with recursive tally_path (
      inp, out, edges, ath, uuids, ents, seqs, signs, min, margin, max, reward, 
      top, top_tseq, bot, bot_tseq, circuit
    ) as (
      select ti.inp, ti.out, 1, array[ti.out], array[ti.uuid], 
             array[ti.tally_ent], array[ti.tally_seq], array[ti.sign],
             ti.min, ti.margin, ti.max, ti.reward, 
             ti.tally_ent, ti.tally_seq, ti.tally_ent, ti.tally_seq, false
    from	mychips.tallies_v_net ti
    where	ti.canlift
  union all
    select tp.inp					as inp
      , t.out						as out
      , tp.edges + 1					as edges
      , tp.ath || t.out					as ath
      , tp.uuids || t.uuid				as uuids
      , tp.ents || t.tally_ent				as ents
      , tp.seqs || t.tally_seq				as seqs
      , tp.signs || t.sign				as signs
      , least(t.min, tp.min)				as min
      , tp.margin + t.margin * (1 - tp.margin)		as margin	-- Aggregated margin

      , case when t.min < tp.min then				-- Will charge only one reward in segment
          least(t.max, tp.min)
        else
          least(t.min, tp.max) end			as max
      , case when t.min < tp.min then t.reward
        else tp.reward end				as reward	-- Only one reward
      , t.tally_ent					as top
      , t.tally_seq					as top_tseq
      , tp.bot						as bot
      , tp.bot_tseq					as bot_tseq
      , coalesce(tp.inp = t.out, false)			as circuit

    from	mychips.tallies_v_net t
    join	tally_path	tp on tp.out = t.inp
    		and not t.uuid = any(tp.uuids)
    		and (t.out isnull or not t.out = any(tp.ath))
    where	t.canlift
  ) select tpr.inp, tpr.out
    , tpr.edges, tpr.ath, tpr.uuids, tpr.ents, tpr.seqs, tpr.signs, tpr.min, tpr.max
    , tpr.top, tpr.bot, tpr.circuit
    , tpr.margin::numeric(8,6)
    , tpr.reward::numeric(8,6)
    , tpr.edges + 1			as nodes
    , tpr.edges * tpr.min		as bang
    , tpr.inp isnull			as fori
    , tpr.out isnull			as foro
    , tpr.inp isnull and tpr.out isnull	as segment
    , tpr.inp || tpr.ath		as path
    , tpr.ath[1:edges-1]		as at
    , tpr.inp || tpr.ath[1:edges-1]	as pat

    , tt.tally_seq as top_tseq, tt.tally_uuid as top_uuid
    , bt.tally_seq as bot_tseq, bt.tally_uuid as bot_uuid

    , tt.hold_cid as top_cid, tt.hold_agent as top_agent, tt.hold_chad as top_chad
    , bt.hold_cid as bot_cid, bt.hold_agent as bot_agent, bt.hold_chad as bot_chad

    , case when out isnull then tt.part_cid else tt.hold_cid end as out_cid, case when out isnull then tt.part_agent else tt.hold_agent end as out_agent, case when out isnull then tt.part_chad else tt.hold_chad end as out_chad
    , case when inp isnull then bt.part_cid else bt.hold_cid end as inp_cid, case when inp isnull then bt.part_agent else bt.hold_agent end as inp_agent, case when inp isnull then bt.part_chad else bt.hold_chad end as inp_chad

  from	tally_path tpr
  join	mychips.tallies_v	tt on tt.tally_ent = tpr.top and tt.tally_seq = tpr.top_tseq
  join	mychips.tallies_v	bt on bt.tally_ent = tpr.bot and bt.tally_seq = tpr.bot_tseq;
create trigger mychips_tallies_v_tr_ins instead of insert on mychips.tallies_v for each row execute procedure mychips.tallies_v_insfunc();
create function mychips.ticket_get(seq int, reu boolean = false, exp timestamp = current_timestamp + '45 minutes') returns jsonb language plpgsql as $$
    declare
      trec	record;
      ent	text = base.curr_eid();
    begin
    
      select into trec token,expires,chad from mychips.tokens_v_me
          where token_ent = ent
          and tally_seq = seq and valid order by crt_date desc limit 1;

      if not found then
        if (select status from mychips.tallies_v_me where tally_ent = ent and tally_seq = seq) != 'draft' then
          return null;
        end if;
        insert into mychips.tokens_v_me (tally_seq, reuse, expires) values (seq, reu, exp)
          returning token, expires, chad into trec;
      end if;
      
      return jsonb_build_object(
        'token',	trec.token,
        'expires',	trec.expires,
        'chad',		trec.chad
      );
    end;
$$;
create view mychips.users_v_tallysum as select 
    u.id, u.std_name, u.user_ent, u.peer_cid, u.peer_agent, u.peer_host, u.peer_port, u.ent_name, u.fir_name, u.ent_type
  , coalesce(s.tallies, 0)			as tallies
  , coalesce(s.net, 0)				as net
  , coalesce(s.stocks, 0)			as stocks
  , coalesce(s.foils, 0)			as foils
  , coalesce(s.clients, '{}'::text[])		as clients
  , coalesce(s.vendors, '{}'::text[])		as vendors
  
  , coalesce(s.part_ents, '{}'::text[])		as part_ents
  , coalesce(s.part_cids, '{}'::text[])		as part_cids
  , coalesce(s.part_agents, '{}'::text[])	as part_agents
  , coalesce(s.uuids, '{}'::uuid[])		as uuids
  , coalesce(s.seqs, '{}'::int[])		as seqs
  , coalesce(s.types, '{}'::tally_side[])	as types
  , coalesce(s.states, '{}'::text[])		as states
  , coalesce(s.nets, '{}'::bigint[])		as nets
  , coalesce(s.insides, '{}'::boolean[])	as insides

  , coalesce(s.targets, '{}'::bigint[])		as targets
  , coalesce(s.rewards, '{}'::float[])		as rewards
  , coalesce(s.bounds, '{}'::bigint[])		as bounds
  , coalesce(s.clutchs, '{}'::float[])		as clutchs
  , coalesce(s.policies, '{}'::jsonb[])		as policies
  
  , coalesce(s.client_cids, '{}'::text[])	as client_cids
  , coalesce(s.client_agents, '{}'::text[])	as client_agents
  , coalesce(s.vendor_cids, '{}'::text[])	as vendor_cids
  , coalesce(s.vendor_agents, '{}'::text[])	as vendor_agents
  , coalesce(s.stock_uuids, '{}'::uuid[])	as stock_uuids
  , coalesce(s.foil_uuids, '{}'::uuid[])	as foil_uuids
  , coalesce(s.stock_seqs, '{}'::int[])		as stock_seqs
  , coalesce(s.foil_seqs, '{}'::int[])		as foil_seqs
  , greatest(coalesce(s.latest, u.mod_date),u.mod_date)	as latest
  , coalesce(s.json, '[]'::jsonb)		as json
    from	mychips.users_v u
    left join	mychips.tallies_v_sum s on s.tally_ent = u.user_ent;
create function json.cert_tf_ii() returns trigger language plpgsql security definer as $$
  declare
    ent_name text = new.name;
    fir_name text;
    mid_name text;
    pref_name text;
    born_date date;
    peer_named text;
    tax_id text;
    country text;
    irec record;
    urec record;
    ident jsonb = new.identity;
    birth_place jsonb;
    pkey jsonb;
  begin

    if (new.type = 'p') then				--Personal names
      ent_name = new.name->>'surname';
      fir_name = new.name->>'first';
      mid_name = new.name->>'middle';
      pref_name = new.name->>'prefer';
    end if;
    if not ident isnull then				--Identity records
      if not ident->'state' isnull then			--State ID
        tax_id = ident->'state'->>'id';
        country = ident->'state'->>'country';
      end if;
      if not ident->'birth' isnull then			--Birth ID
        birth_place = ident->'birth'->'place';
        born_date = (ident->'birth'->>'date')::date;
        peer_named = ident->'birth'->>'name';
      end if;
    end if;

    select into urec * from mychips.users_v u where	--Do we already have this person
      u.peer_psig = new.public or (u.peer_cid = new.chad->>'cid' and u.peer_agent = new.chad->>'agent');





    insert into mychips.users_v (ent_name, fir_name, mid_name, pref_name, ent_type, born_date, tax_id, country, peer_cid, peer_agent, peer_host, peer_port, peer_psig, peer_named)
      values (ent_name, fir_name, mid_name, pref_name, new.type, born_date, tax_id, country, new.chad->>'cid', new.chad->>'agent', new.chad->>'host', (new.chad->>'port')::int, new.public, peer_named)





      returning id into irec;
    new.id = irec.id;
    
    pkey = to_jsonb(irec);

    perform json.import(to_jsonb(new.connect), 'connect', pkey);
    perform json.import(to_jsonb(new.place), 'place', pkey);
    if not birth_place isnull then
      birth_place = jsonb_set(birth_place, '{type}', '"birth"');
      perform json.import(birth_place, 'place', pkey);
    end if;
    return new;
  end;
$$;
create trigger mychips_chits_tr_notice after insert or update on mychips.chits for each row execute procedure mychips.chits_tf_notify();
create function mychips.lift_local(maxNum int = 1) returns jsonb language plpgsql security definer as $$
    declare
      status	jsonb = '{"done": 0}';
      prec	record;
      orders	text default 'bang desc';
      tstr	text;
      tarr	text[];
      oarr	text[];
      lift_id	uuid;
      min_units	int default base.parm('lifts','minimum',1);
      ord_by	text default base.parm('lifts','order','bang desc'::text);
      count	int default 0;
      rows	int;
    begin
raise notice 'LL0:% % %', maxNum, min_units, ord_by;
      foreach tstr in array regexp_split_to_array(ord_by, ',') loop
        oarr = regexp_split_to_array(btrim(tstr), E'\\s+');
raise notice 'LL1 tstr:% el0:%', tstr, oarr[1];
        tarr = array_append(tarr, quote_ident(oarr[1]) || case when oarr[2] = 'desc' then ' desc' else '' end);
      end loop;
      orders = array_to_string(tarr, ', ');
raise notice 'LL2 orders:%', orders;

      while count < maxNum loop			-- Search for internal lifts
        tstr = 'select uuids, min
          from mychips.tallies_v_paths where circuit and margin <= 0 and 
          min >= $1 order by ' || orders || ' limit 1';
        execute tstr into prec using min_units;
        get diagnostics rows = ROW_COUNT;
raise notice 'LL3 rows:% min:% tstr:%', rows, min_units, tstr;
        if rows < 1 then exit; end if;

        insert into mychips.lifts (lift_type, circuit, status, units, tallies)
          values ('in', true, 'good', prec.min, prec.uuids);
        count = count + 1;
      end loop;
    return jsonb_set(status, '{done}', count::text::jsonb);
    end;
$$;
create function mychips.lift_notify(lift mychips.lifts) returns boolean language plpgsql security definer as $$
    declare
        channel		text;
        jret		jsonb;
        jmerge		jsonb = '{}';
        lrec		record;
        rrec		record;
    begin
raise notice 'Lift request:%', lift.request;

      select into lrec json, circuit, find_v, origin_v, referee_v,
        inp_chad, bot_chad, bot_tally,
        top_chad, out_chad, top_tally
        from mychips.lifts_v_dist
          where lift_uuid = lift.lift_uuid and lift_seq = lift.lift_seq;

      if lift.request in ('found','void') then		-- Outgoing message will be downstream
        channel = 'ma_' || (lrec.bot_chad->>'agent');

      else					-- Outgoing message will be upstream
        channel = 'ma_' || (lrec.top_chad->>'agent');
        if lift.request = 'init' then		-- Init gets extra payload
          jmerge = jmerge || jsonb_build_object(
            'init', jsonb_build_object(
              'find',		lrec.find_v
            , 'org',		lrec.origin_v
            , 'ref',		lrec.referee_v
            , 'circuit',	lrec.circuit));
        end if;
      end if;

      jret = jsonb_build_object('target', 'lift'
        , 'action',	lift.request
        , 'sequence',	lift.lift_seq
        , 'outc',	lrec.out_chad
        , 'topc',	lrec.top_chad
        , 'topt',	lrec.top_tally
        , 'inpc',	lrec.inp_chad
        , 'botc',	lrec.bot_chad
        , 'bott',	lrec.bot_tally
        , 'object',	lrec.json
      ) || jmerge;

raise notice 'Lift notice:% %', channel, jret::text;
      if channel notnull then
        perform pg_notify(channel, jret::text);
      end if;
      return true;
    end;
$$;
create trigger mychips_lifts_v_tr_ins instead of insert on mychips.lifts_v for each row execute procedure mychips.lifts_v_insfunc();
create trigger mychips_lifts_v_tr_upd instead of update on mychips.lifts_v for each row execute procedure mychips.lifts_v_updfunc();
create function mychips.routes_find(base record, dest jsonb, currStep int, avoid text) returns jsonb language plpgsql security definer as $$
    declare
      lrec	record;
      jtmp	jsonb;
      lading	jsonb;
      forward	int = 0;
      maxQuery	int = base.parm('routes', 'maxquery', 12);
    begin

      for lrec in		-- Hypothetical paths to destination
        with tp as (		-- Like routes_v_query but for destination that may not be in the DB
          select bot, bot_tseq, top, top_tseq, out_cid, out_agent, fori, foro, at,
            dest->>'cid' as find_cid, dest->>'agent' as find_agent	-- may (or not) already exist
          from mychips.tallies_v_paths where bot = base.tally_ent and bot_tseq = base.tally_seq
        )
        select mychips.route_sorter(r.status,r.expired) as sorter,
            tp.bot, tp.bot_tseq, tp.top, tp.top_tseq, tp.foro, tp.at,
            tp.out_cid, tp.out_agent, tp.fori, tp.find_cid, tp.find_agent,
            r.status, r.dst_cid, r.dst_agent,	r.min,r.max,r.margin,r.reward, r.expired
        from tp					-- overlaid by those that already  exist
        left join mychips.routes_v r on r.via_ent = tp.top and r.via_tseq = tp.top_tseq
                                    and r.dst_cid = tp.find_cid and r.dst_agent = tp.find_agent
        where	tp.fori and tp.foro and tp.foro
        and	(avoid isnull or not (avoid = any(tp.at)))			-- If we've already found a local path
        and	not (tp.out_cid = tp.find_cid and tp.out_agent = tp.find_agent)	-- If we're already connected to this peer directly
        order by 1,r.rid,tp.top,tp.top_tseq limit maxQuery loop
        
        jtmp = mychips.route_pop(lrec, currStep);
        forward = forward + (jtmp->'forward')::int;
        lading = coalesce(jtmp->'lading', lading);
      end loop;

      return jsonb_build_object(
        'action',	case when forward > 0 then 'relay' else 'none' end,
        'forward',	forward,
        'lading',	lading
      );
    end;
$$;
create function mychips.routes_tf_notify() returns trigger language plpgsql security definer as $$
    declare
        dirty	boolean default false;
    begin
        if TG_OP = 'INSERT' then
            dirty = true;
        elsif new.status != old.status then
            dirty = true;
        end if;
        if dirty then perform mychips.route_notify(new); end if;
        return new;
    end;
$$;
create view mychips.routes_v_paths as select
    tp.inp, tp.out, tp.top, tp.top_tseq, tp.bot, tp.bot_tseq
  , tp.edges, tp.nodes, tp.at, tp.pat, tp.ath, tp.path, tp.uuids, tp.ents, tp.seqs
  , tp.fori, tp.foro, tp.segment, tp.bang
  , tp.top_uuid, tp.top_cid, tp.top_agent, tp.top_chad
  , tp.bot_uuid, tp.bot_cid, tp.bot_agent, tp.bot_chad
  , tp.out_cid, tp.out_agent, tp.out_chad
  , tp.inp_cid, tp.inp_agent, tp.inp_chad
  , r.rid, r.via_ent, r.via_tseq, r.via_tally
  , r.dst_cid, r.dst_agent
  , r.req_ent, r.req_tseq, r.req_tally, r.req_cid, r.req_agent, r.req_chad
  , r.rpt_cid, r.rpt_agent, r.rpt_chad
  , r.status
  , r.lift_count
  , r.native
  , r.dst_cid = tp.inp_cid and r.dst_agent = tp.inp_agent as circuit
  , tp.min	as path_min,	tp.margin::numeric(8,6)	as path_margin
  , tp.max	as path_max,	tp.reward::numeric(8,6)	as path_reward
  , r.min	as route_min,	r.margin::numeric(8,6)	as route_margin
  , r.max	as route_max,	r.reward::numeric(8,6)	as route_reward
  
  , least(tp.min, r.min)				as min
  , case when r.min < tp.min then
        least(r.max, tp.min)
      else
        least(r.min, tp.max) end			as max
  , (r.margin + tp.margin * (1-r.margin))::numeric(8,6)	as margin
  , case when r.min < tp.min then r.reward
      else tp.reward end::numeric(8,6)			as reward

  from	mychips.routes_v	r
  join	mychips.tallies_v_paths	tp on tp.top = r.via_ent and tp.top_tseq = r.via_tseq and tp.foro;
create trigger mychips_routes_v_tr_ins instead of insert on mychips.routes_v for each row execute procedure mychips.routes_v_insfunc();
create trigger mychips_routes_v_tr_upd instead of update on mychips.routes_v for each row execute procedure mychips.routes_v_updfunc();
create trigger json_cert_tf_ii instead of insert on json.cert for each row execute procedure json.cert_tf_ii();
create function mychips.lift_dist(maxNum int = 1) returns int language plpgsql as $$
    declare
      prec	record;
      tstr	text;
      tarr	text[];
      oarr	text[];
      orders	text default 'bang desc';
      min_units	int default base.parm('lifts','minimum',1);
      ord_by	text default base.parm('lifts','order','bang desc'::text);
      count	int = 0;
      rows	int;
    begin
raise notice 'LD0:% % %', maxNum, min_units, ord_by;
      foreach tstr in array regexp_split_to_array(ord_by, ',') loop
        oarr = regexp_split_to_array(btrim(tstr), E'\\s+');

        tarr = array_append(tarr, quote_ident(oarr[1]) || case when oarr[2] = 'desc' then ' desc' else '' end);
      end loop;
      orders = array_to_string(tarr, ', ');
raise notice 'LD2 orders:%', orders;

      while count < maxNum loop			-- Search for internal lifts

        tstr = 'select uuids, min
          from mychips.routes_v_paths where segment and status = ''good'' and
             min >= $1 order by ' || orders || ' limit 1';
        execute tstr into prec using min_units;
        get diagnostics rows = ROW_COUNT;
raise notice 'LD3 rows:% min:% tstr:%', rows, min_units, tstr;
        if rows < 1 then exit; end if;
      
        insert into mychips.lifts (lift_type, circuit, request, units, tallies)
          values ('org', true, 'init', prec.min, prec.uuids);
        count = count + 1;
      end loop;
      return count;
    end;
$$;
create function mychips.route_circuit(ent text default null, seq int default null) returns jsonb language plpgsql as $$
    declare
      trec	record;
      dest	jsonb;
      results	jsonb = '[]';
    begin

      if ent isnull then			-- Generate all possible routes
        for trec in select bot, bot_tseq, top, top_tseq,
            out_cid, out_agent, find_cid, find_agent,
            status, dst_cid, dst_agent,	min,max,margin,reward, expired, sorter
          from mychips.routes_v_query order by sorter loop
            results = results || mychips.route_pop(trec);
        end loop;

      else					-- Generate routes for a user or tally
        for trec in select distinct bot as tally_ent, bot_tseq as tally_seq,
                inp_cid, inp_chad, top, top_tseq
          from	mychips.tallies_v_paths
          where	top = ent and (seq isnull or top_tseq = seq) and fori loop

            results = results || mychips.routes_find(trec, trec.inp_chad, 0, null);
        end loop;
      end if;
      return results;
    end;
$$;
create function mychips.route_linear(ent text, dest jsonb) returns jsonb language plpgsql as $$
    declare
      trec	record;
      results	jsonb = '[]';
    begin
      for trec in select distinct inp as tally_ent, bot_tseq as tally_seq
        from	mychips.tallies_v_net where inp = ent loop
raise notice 'Route Linear check: %:%', trec.inp, dest;
             results = results || mychips.routes_find(trec, dest, 0, null);
      end loop;
      return results;
    end;
$$;
create function mychips.route_process(msg jsonb, recipe jsonb) returns jsonb language plpgsql as $$
    declare
        to_chad		jsonb = msg->'to';
        fr_chad		jsonb = msg->'from';
        obj		jsonb = msg->'object';
        find		jsonb = obj->'find';
        retObj		jsonb;
        currStep	int = coalesce((obj->'step')::int, 0);
        maxStep		int;
        dest		record;
        route		record;
        base		record;
        path		record;
        qstrg		text;
        xrec		record;
        curState	text;
    begin


        select into base tally_ent, tally_seq, tally_uuid, hold_cid, hold_agent, part_cid, part_agent
          from mychips.tallies_v where
            tally_uuid = (obj->>'tally')::uuid and liftable;
        if not found then return null; end if;




        if base.part_cid   is distinct from fr_chad->>'cid'   or 
           base.part_agent is distinct from fr_chad->>'agent' or
           base.hold_cid   is distinct from to_chad->>'cid'   or 
           base.hold_agent is distinct from to_chad->>'agent' then

             return null;
        end if;

        select into dest id, peer_cid, peer_host from mychips.users_v where peer_cid = find->>'cid' and peer_agent = find->>'agent';


        if recipe->'query' then			-- If there a query flag in the recipe object
          maxStep = base.parm('routes', 'maxstep', 20);

          if not dest.id isnull then			-- Is the destination a local user?
            select into path inp,out,min,max,margin,reward from mychips.tallies_v_paths		-- Do we have a direct path to him?
              where bot = base.tally_ent and bot_tseq = base.tally_seq and top = dest.id
                order by margin, min desc limit 1;


            if found or  currStep <= maxStep then	-- See if there are any indirect, external routes we should also search
              retObj = mychips.routes_find(base, find, currStep, dest.id);
            end if;

          elsif currStep <= maxStep then -- destination is not local but we will to search for it

            select into path inp,out,min,max,margin,reward from mychips.tallies_v_paths		-- Do we have a direct path to him?
              where bot = base.tally_ent and bot_tseq = base.tally_seq
                and out_cid = find->>'cid' and out_agent = find->>'agent'
                order by margin, min desc limit 1;


            retObj = mychips.routes_find(base, find, currStep, null::text);
          end if;


          if not path isnull then
            retObj = retObj || jsonb_build_object(
              'action',	'good',
              'lading',	jsonb_build_object(
                  'min',	path.min,	'max',		path.max,
                  'margin',	path.margin,	'reward',	path.reward
              ));
          end if;
          return retObj;
        end if;

        if recipe ? 'update' then
          select into route * from mychips.routes_v where via_cid = to_chad->>'cid' and via_tally = (obj->>'tally')::uuid;
          curstate = coalesce(route.state,'null');


          if not (jsonb_build_array(curState) <@ (recipe->'context')) then	--Not in any applicable state (listed in our recipe context)
raise notice 'RZ:% C:%', jsonb_build_array(curState), recipe->'context';
            return to_jsonb(curState);
          end if;

          if not route.rid isnull then
            qstrg = mychips.state_updater(recipe, 'mychips.routes_v', '{status, min, margin, max, reward}', '{"good_date = current_timestamp"}');

            execute qstrg || 'rid = $1 returning rid, state' into route using route.rid;
            if recipe->'update'->>'status' in ('good','none') then	-- Resolution found, delete retry counter
              delete from mychips.route_tries where rtry_rid = route.rid;
            end if;
          end if;
          return to_jsonb(route.state);
        end if;
      return null;
    end;
$$;
create trigger mychips_routes_tr_notice after insert or update on mychips.routes for each row execute procedure mychips.routes_tf_notify();
create view mychips.routes_v_query as select tp.*
  , r.rid, r.via_ent, r.via_tseq, r.via_tally
  , r.dst_cid, r.dst_agent, r.status, r.expired
  , mychips.route_sorter(r.status, r.expired)	as sorter
  , r.via_ent is not null			as exist
  , tp.inp_cid 					as find_cid
  , tp.inp_agent				as find_agent
  
  from mychips.tallies_v_paths	tp
  left join mychips.routes_v	r on r.via_ent = tp.top and r.via_tseq = tp.top_tseq and
                                     r.dst_cid = tp.inp_cid and r.dst_agent = tp.inp_agent
  where tp.segment;
create function mychips.tallies_tf_notify() returns trigger language plpgsql security definer as $$
    declare
      notify	boolean default false;
    begin
      if TG_OP = 'INSERT' and not new.request isnull then
        notify = true;
      else			-- This is an update
        if not new.request isnull and new.request is distinct from old.request then
          notify = true;
        end if;
        if new.request is null and new.status = 'open' and old.status != 'open' then
          if base.parm_boolean('routes', 'autoquery') then
            perform mychips.route_circuit(new.tally_ent, new.tally_seq);
          end if;
        end if;
      end if;
      if notify then perform mychips.tally_notify_agent(new); end if;
      return new;
    end;
$$;
create trigger mychips_tallies_tr_notice after insert or update on mychips.tallies for each row execute procedure mychips.tallies_tf_notify();

--Data Dictionary:
insert into wm.table_text (tt_sch,tt_tab,language,title,help) values
  ('base','addr','eng','Addresses','Addresses (home, mailing, etc.) pertaining to entities'),
  ('base','addr_prim','eng','Primary Address','Internal table to track which address is the main one for each given type'),
  ('base','addr_v','eng','Addresses','A view of addresses (home, mailing, etc.) pertaining to entities, with additional derived fields'),
  ('base','addr_v_flat','eng','Entities Flat','A flattened view of entities showing their primary standard addresses'),
  ('base','comm','eng','Communication','Communication points (phone, email, fax, etc.) for entities'),
  ('base','comm_prim','eng','Primary Communication','Internal table to track which communication point is the main one for each given type'),
  ('base','comm_v','eng','Communication','View of users'' communication points (phone, email, fax, etc.) with additional helpful fields'),
  ('base','comm_v_flat','eng','Entities Flat','A flattened view of entities showing their primary standard contact points'),
  ('base','country','eng','Countries','Contains standard ISO data about international countries'),
  ('base','ent','eng','Entities','Entities, which can be a person, a company or a group'),
  ('base','ent_audit','eng','Entities Auditing','Table tracking changes to the entities table'),
  ('base','ent_link','eng','Entity Links','Links to show how one entity (like an employee) is linked to another (like his company)'),
  ('base','ent_link_v','eng','Entity Links','A view showing links to show how one entity (like an employee) is linked to another (like his company), plus the derived names of the entities'),
  ('base','ent_v','eng','Entities','A view of Entities, which can be a person, a company or a group, plus additional derived fields'),
  ('base','ent_v_pub','eng','Entities Public','A view of Entities from which ever user can access certain public information'),
  ('base','file','eng','Document Files','Document files (photos, computer files, etc.) for entities'),
  ('base','file_prim','eng','Primary Files','Internal table to track which file is the main one for each given type'),
  ('base','file_v','eng','Document Files','View of users'' files with additional helpful fields'),
  ('base','language','eng','Languages','Contains information  about international ISO language codes'),
  ('base','language_v','eng','Languages','Contains information about about international ISO language codes'),
  ('base','parm','eng','System Parameters','Contains parameter settings of several types for configuring and controlling various modules across the database'),
  ('base','parm_audit','eng','Parameters Auditing','Table tracking changes to the parameters table'),
  ('base','parm_v','eng','Parameters','System parameters are stored in different tables depending on their data type (date, integer, etc.).  This view is a union of all the different type tables so all parameters can be viewed and updated in one place.  The value specified will have to be entered in a way that is compatible with the specified type so it can be stored natively in its correct data type.'),
  ('base','priv','eng','Privileges','Permissions assigned to each system user defining what tasks they can perform and what database objects they can access'),
  ('base','priv_v','eng','Privileges','Privileges assigned to each entity'),
  ('base','token','eng','Access Tokens','Stores access codes which allow users to connect for the first time'),
  ('base','token_v','eng','Tokens','A view of the access codes, which allow users to connect for the first time'),
  ('base','token_v_ticket','eng','Login Tickets','A view of the access codes, which allow users to connect for the first time'),
  ('json','cert','eng','JSON Certificate','JSON view of user certificates primarily meant for import/export'),
  ('mychips','addr_v_me','eng','User Addresses','A view of the current user''s partners'' addresses'),
  ('mychips','agents','eng','Site Agents','Maintains the connection addresses of agent processes'),
  ('mychips','chit_tries','eng','Chit Retries','Tracks how many times the chit state transition algorithm has tried to communicate a transition to a peer'),
  ('mychips','chits','eng','Chits','Contains an entry for each transaction of credit flow in either direction between the parties to the tally.'),
  ('mychips','chits_v','eng','Chits','Standard view containing an entry for each chit, which is a transmission of value between two trading partners on a single tally.'),
  ('mychips','chits_v_chains','eng','Chit Chains','Contains information about hash-linked chains of value transfer (chit) records'),
  ('mychips','chits_v_me','eng','My Chits','View of all transactions on the tallies of the current user'),
  ('mychips','comm_v_me','eng','User Contact','A view of the current user''s partners'' communication points'),
  ('mychips','contracts','eng','Contracts','Each record contains contract language to be included by reference in a MyCHIPs tally or a similar agreement'),
  ('mychips','contracts_v','eng','Contracts','Each record contains contract language to be included by reference in a MyCHIPs tally or a similar agreement.'),
  ('mychips','lifts','eng','Lifts','Contains a record for each group of chits in a segment, belonging to a lift transaction'),
  ('mychips','lifts_v','eng','Lifts','Standard view containing an entry for each lift with additional helpful derived fields'),
  ('mychips','lifts_v_dist','eng','Distributed Lifts','Standard view containing an entry for each lift with additional helpful derived fields applicable to distributed (not local) lifts'),
  ('mychips','route_tries','eng','Route Retries','Tracks how many times the route state transition algorithm has tried to communicate a transition to a peer'),
  ('mychips','routes','eng','Foreign Routes','Information collected from other servers about foreign peers that can be reached by way of established tallies'),
  ('mychips','routes_v','eng','Foreign Routes','A view showing foreign peers that can be reached by way of one of our known foreign peers'),
  ('mychips','tallies','eng','Tallies','Contains an entry for each tally, which is a record of credit transactions between two trading partners.'),
  ('mychips','tallies_v','eng','Tallies','Standard view containing an entry for each tally, which is a record of credit transactions between two trading partners.'),
  ('mychips','tallies_v_me','eng','My Tallies','View containing the tallies pertaining to the current user'),
  ('mychips','tallies_v_net','eng','Tally Lift Edges','A view showing a single link between entities hypothetially eligible for a lift'),
  ('mychips','tallies_v_paths','eng','Tally Pathways','A view showing network pathways between local entities, based on the tallies they have in place'),
  ('mychips','tally_tries','eng','Tally Retries','Table contains information about retries with peers to establish tallies'),
  ('mychips','tokens','eng','Tokens','Tracks one-time connection tokens for foreign peers'),
  ('mychips','users','eng','CHIP Users','Entities who have CHIP accounts on this server'),
  ('mychips','users','fin','CHIP käyttäjät','Yksiköt, joilla on CHIP-tilejä tällä palvelimella'),
  ('mychips','users_v','eng','CHIP Users','Entities who have CHIP accounts on this server.'),
  ('mychips','users_v','fin','CHIP käytäjät näkymä','Yksiköt, joilla on CHIP-tilejä tällä palvelimella'),
  ('mychips','users_v_me','eng','Current User','A view containing only the current user''s data'),
  ('mychips','users_v_tallies','eng','Users and Tallies','View primarily for simulations and network visualizer'),
  ('wm','column_ambig','eng','Ambiguous Columns','A view showing view and their columns for which no definitive native table and column can be found automatically'),
  ('wm','column_data','eng','Column Data','Contains information from the system catalogs about columns of tables in the system'),
  ('wm','column_def','eng','Column Default','A view used internally for initializing columns to their default value'),
  ('wm','column_istyle','eng','Column Styles','A view of the default display styles for table and view columns'),
  ('wm','column_lang','eng','Column language','A view of descriptive language data as it applies to the columns of tables and views'),
  ('wm','column_meta','eng','Column Metadata','A view of data about the use and display of the columns of tables and views'),
  ('wm','column_native','eng','Native Columns','Contains cached information about the tables and their columns which various higher level view columns derive from.  To query this directly from the information schema is somewhat slow, so wyseman caches it here when building the schema for faster access.'),
  ('wm','column_pub','eng','Columns','Joins information about table columns from the system catalogs with the text descriptions defined in wyseman'),
  ('wm','column_style','eng','Column Styles','Contains style flags to tell the GUI how to render the columns of a table or view'),
  ('wm','column_text','eng','Column Text','Contains a description for each column of each table in the system'),
  ('wm','fkey_data','eng','Key Data','Includes data from the system catalogs about how key fields in a table point to key fields in a foreign table.  Each separate key field is listed as a separate row.'),
  ('wm','fkey_pub','eng','Key Info','Public view to see foreign key relationships between views and tables and what their native underlying tables/columns are.  One row per key column.'),
  ('wm','fkeys_data','eng','Keys Data','Includes data from the system catalogs about how key fields in a table point to key fields in a foreign table.  Each key group is described on a separate row.'),
  ('wm','fkeys_pub','eng','Keys','Public view to see foreign key relationships between views and tables and what their native underlying tables/columns are.  One row per key group.'),
  ('wm','lang','eng','Language Text','Language messages pertaining to Wyseman service routines'),
  ('wm','message_text','eng','Message Text','Contains messages in a particular language to describe an error, or a widget feature or button'),
  ('wm','objects','eng','Objects','Keeps data on database tables, views, functions, etc. telling how to build or drop each object and how it relates to other objects in the database.'),
  ('wm','objects_v','eng','Rel Objects','An enhanced view of the object table, expanded by showing the full object specifier, and each separate release this version of the object belongs to'),
  ('wm','objects_v_dep','eng','Dependencies','A recursive view showing which database objects depend on (must be created after) other database objects.'),
  ('wm','objects_v_depth','eng','Dep Objects','An enhanced view of the object table, expanded by showing the full object specifier, each separate release this version of the object belongs to, and the maximum depth it is along any path in the dependency tree.'),
  ('wm','objects_v_max','eng','Latest Objects','Updatable view of database objects with the largest, most current version number'),
  ('wm','objects_v_next','eng','Next Objects','View of database objects with the working release version number'),
  ('wm','releases','eng','Releases','Tracks the version number of each public release of the database design'),
  ('wm','role_members','eng','Role Members','Summarizes information from the system catalogs about members of various defined roles'),
  ('wm','table_data','eng','Table Data','Contains information from the system catalogs about views and tables in the system'),
  ('wm','table_lang','eng','Table Language','A view of titles and descriptions of database tables/views'),
  ('wm','table_meta','eng','Table Metadata','A view of data about the use and display of tables and views'),
  ('wm','table_pub','eng','Tables','Joins information about tables from the system catalogs with the text descriptions defined in wyseman'),
  ('wm','table_style','eng','Table Styles','Contains style flags to tell the GUI how to render each table or view'),
  ('wm','table_text','eng','Table Text','Contains a description of each table in the system'),
  ('wm','value_text','eng','Value Text','Contains a description for the values which certain columns may be set to.  Used only for columns that can be set to one of a finite set of values (like an enumerated type).'),
  ('wm','view_column_usage','eng','View Column Usage','A version of a similar view in the information schema but faster.  For each view, tells what underlying table and column the view column uses.'),
  ('wylib','data','eng','GUI Data','Configuration and preferences data accessed by Wylib view widgets'),
  ('wylib','data','fin','GUI Data','Wylib-näkymäkomponenttien käyttämät konfigurointi- ja asetustiedot'),
  ('wylib','data_v','eng','GUI Data','A view of configuration and preferences data accessed by Wylib view widgets');
insert into wm.column_text (ct_sch,ct_tab,ct_col,language,title,help) values
  ('base','addr','addr_cmt','eng','Comment','Any other notes about this address'),
  ('base','addr','addr_ent','eng','Entity ID','The ID number of the entity this address applies to'),
  ('base','addr','addr_inact','eng','Inactive','This address is no longer a valid address'),
  ('base','addr','addr_prim','eng','Primary','If checked this is the primary address for contacting this entity'),
  ('base','addr','addr_priv','eng','Private','This address should not be shared publicly'),
  ('base','addr','addr_seq','eng','Sequence','A unique number assigned to each new address for a given entity'),
  ('base','addr','addr_spec','eng','Address','Street address or PO Box.  This can occupy multiple lines if necessary'),
  ('base','addr','addr_type','eng','Type','The kind of address'),
  ('base','addr','city','eng','City','The name of the city this address is in'),
  ('base','addr','country','eng','Country','The name of the country this address is in.  Use standard international country code abbreviations.'),
  ('base','addr','crt_by','eng','Created By','The user who entered this record'),
  ('base','addr','crt_date','eng','Created','The date this record was created'),
  ('base','addr','dirty','eng','Dirty','A flag used in the database backend to track whether the primary address needs to be recalculated'),
  ('base','addr','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','addr','mod_date','eng','Modified','The date this record was last modified'),
  ('base','addr','pcode','eng','Zip/Postal','Zip or other mailing code applicable to this address.'),
  ('base','addr','state','eng','State','The name of the state or province this address is in'),
  ('base','addr_prim','prim_ent','eng','Entity','The entity ID number of the main address'),
  ('base','addr_prim','prim_seq','eng','Sequence','The sequence number of the main address'),
  ('base','addr_prim','prim_type','eng','type','The address type this record applies to'),
  ('base','addr_v','addr_prim','eng','Primary','If true this is the primary address for contacting this entity'),
  ('base','addr_v','std_name','eng','Entity Name','The name of the entity this address pertains to'),
  ('base','addr_v_flat','bill_addr','eng','Bill Address','First line of the billing address'),
  ('base','addr_v_flat','bill_city','eng','Bill City','Billing address city'),
  ('base','addr_v_flat','bill_country','eng','Bill Country','Billing address country'),
  ('base','addr_v_flat','bill_pcode','eng','Bill Postal','Billing address postal code'),
  ('base','addr_v_flat','bill_state','eng','Bill State','Billing address state'),
  ('base','addr_v_flat','mail_addr','eng','Mailing Address','First line of the mailing address'),
  ('base','addr_v_flat','mail_city','eng','Mailing City','Mailing address city'),
  ('base','addr_v_flat','mail_country','eng','Mailing Country','Mailing address country'),
  ('base','addr_v_flat','mail_pcode','eng','Mailing Postal','ailing address postal code'),
  ('base','addr_v_flat','mail_state','eng','Mailing State','Mailing address state'),
  ('base','addr_v_flat','phys_addr','eng','Physical Address','First line of the physical address'),
  ('base','addr_v_flat','phys_city','eng','Physical City','Physical address city'),
  ('base','addr_v_flat','phys_country','eng','Physical Country','Physical address country'),
  ('base','addr_v_flat','phys_pcode','eng','Physical Postal','Physical address postal code'),
  ('base','addr_v_flat','phys_state','eng','Physical State','Physical address state'),
  ('base','addr_v_flat','ship_addr','eng','Ship Address','First line of the shipping address'),
  ('base','addr_v_flat','ship_city','eng','Ship City','Shipping address city'),
  ('base','addr_v_flat','ship_country','eng','Ship Country','Shipping address country'),
  ('base','addr_v_flat','ship_pcode','eng','Ship Postal','Shipping address postal code'),
  ('base','addr_v_flat','ship_state','eng','Ship State','Shipping address state'),
  ('base','comm','comm_cmt','eng','Comment','Any other notes about this communication point'),
  ('base','comm','comm_ent','eng','Entity','The ID number of the entity this communication point belongs to'),
  ('base','comm','comm_inact','eng','Inactive','This record is no longer currently in use'),
  ('base','comm','comm_prim','eng','Primary','If checked this is the primary method of this type for contacting this entity'),
  ('base','comm','comm_priv','eng','Private','This record should not be shared publicly'),
  ('base','comm','comm_seq','eng','Sequence','A unique number assigned to each new communication point for a given entity'),
  ('base','comm','comm_spec','eng','Num/Addr','The number or address to use when communication via this method and communication point'),
  ('base','comm','comm_type','eng','Medium','The method of communication'),
  ('base','comm','crt_by','eng','Created By','The user who entered this record'),
  ('base','comm','crt_date','eng','Created','The date this record was created'),
  ('base','comm','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','comm','mod_date','eng','Modified','The date this record was last modified'),
  ('base','comm_prim','prim_ent','eng','Entity','The entity ID number of the main communication point'),
  ('base','comm_prim','prim_seq','eng','Sequence','The sequence number of the main communication point'),
  ('base','comm_prim','prim_spec','eng','Medium','The communication type this record applies to'),
  ('base','comm_prim','prim_type','eng','type','The communication type this record applies to'),
  ('base','comm_v','comm_prim','eng','Primary','If true this is the primary method of this type for contacting this entity'),
  ('base','comm_v','std_name','eng','Entity Name','The name of the entity this communication point pertains to'),
  ('base','comm_v_flat','cell_comm','eng','Cellular','The contact''s cellular phone number'),
  ('base','comm_v_flat','email_comm','eng','Email','The contact''s email address'),
  ('base','comm_v_flat','fax_comm','eng','Fax','The contact''s FAX number'),
  ('base','comm_v_flat','other_comm','eng','Other','Some other communication point for the contact'),
  ('base','comm_v_flat','pager_comm','eng','Pager','The contact''s pager number'),
  ('base','comm_v_flat','phone_comm','eng','Phone','The contact''s telephone number'),
  ('base','comm_v_flat','text_comm','eng','Text Message','An email address that will send text to the contact''s phone'),
  ('base','comm_v_flat','web_comm','eng','Web Address','The contact''s web page'),
  ('base','country','capital','eng','Capital','The name of the capital city'),
  ('base','country','code','eng','Country Code','The ISO 2-letter country code.  This is the offical value to use when entering countries in wylib applications.'),
  ('base','country','com_name','eng','Country','The common name of the country in English'),
  ('base','country','cur_code','eng','Currency','The standard code for the currency of this country'),
  ('base','country','cur_name','eng','Curr Name','The common name in English of the currency of this country'),
  ('base','country','dial_code','eng','Dial Code','The numeric code to dial when calling this country on the phone'),
  ('base','country','iana','eng','Root Domain','The standard extension for WWW domain names for this country'),
  ('base','country','iso_3','eng','Code 3','The ISO 3-letter code for this country (not the wylib standard)'),
  ('base','ent','_last_addr','eng','Addr Sequence','A field used internally to generate unique, sequential record numbers for address records'),
  ('base','ent','_last_comm','eng','Comm Sequence','A field used internally to generate unique, sequential record numbers for communication records'),
  ('base','ent','bank','eng','Bank Routing','Bank routing information: bank_number<:.;,>account_number'),
  ('base','ent','born_date','eng','Born Date','Birth date for person entities or optionally, an incorporation date for entities'),
  ('base','ent','conn_pub','eng','Connection Key','The public key this user uses to authorize connection to the database'),
  ('base','ent','country','eng','Country','The country of primary citizenship (for people) or legal organization (companies)'),
  ('base','ent','crt_by','eng','Created By','The user who entered this record'),
  ('base','ent','crt_date','eng','Created','The date this record was created'),
  ('base','ent','ent_cmt','eng','Ent Comment','Any other notes relating to this entity'),
  ('base','ent','ent_inact','eng','Inactive','A flag indicating that this entity is no longer current, in business, alive, etc'),
  ('base','ent','ent_name','eng','Entity Name','Company name, personal surname, or group name'),
  ('base','ent','ent_num','eng','Entity Number','A number assigned to each entity, unique within its own group of entities with the same type'),
  ('base','ent','ent_type','eng','Entity Type','The kind of entity this record represents'),
  ('base','ent','fir_name','eng','First Name','First given (Robert, Susan, William etc.) for person entities only'),
  ('base','ent','gender','eng','Gender','Whether the person is male (m) or female (f)'),
  ('base','ent','id','eng','Entity ID','A unique code assigned to each entity, consisting of the entity type and number'),
  ('base','ent','marital','eng','Marital Status','Whether the person is married (m) or single (s)'),
  ('base','ent','mid_name','eng','Middle Names','One or more middle given or maiden names, for person entities only'),
  ('base','ent','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','ent','mod_date','eng','Modified','The date this record was last modified'),
  ('base','ent','pref_name','eng','Preferred','Preferred first name (Bob, Sue, Bill etc.) for person entities only'),
  ('base','ent','tax_id','eng','TID/SSN','The number by which the country recognizes this person or company for taxation purposes'),
  ('base','ent','title','eng','Title','A title that prefixes the name (Mr., Chief, Dr. etc.)'),
  ('base','ent','username','eng','Username','The login name for this person, if a user on this system'),
  ('base','ent_audit','a_action','eng','Action','The operation that produced the change (update, delete)'),
  ('base','ent_audit','a_by','eng','Altered By','The username of the user who made the change'),
  ('base','ent_audit','a_date','eng','Date/Time','Date and time of the change'),
  ('base','ent_audit','a_seq','eng','Sequence','A sequential number unique to each alteration'),
  ('base','ent_audit','a_values','eng','Values','JSON object containing the old values of the record before the change'),
  ('base','ent_audit','id','eng','Entity ID','The ID of the entity that was changed'),
  ('base','ent_link','crt_by','eng','Created By','The user who entered this record'),
  ('base','ent_link','crt_date','eng','Created','The date this record was created'),
  ('base','ent_link','mem','eng','Member ID','The ID of the entity that is a member of the organization'),
  ('base','ent_link','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','ent_link','mod_date','eng','Modified','The date this record was last modified'),
  ('base','ent_link','org','eng','Organization ID','The ID of the organization entity that the member entity belongs to'),
  ('base','ent_link','role','eng','Member Role','The function or job description of the member within the organization'),
  ('base','ent_link','supr_path','eng','Super Chain','An ordered list of superiors from the top down for this member in this organization'),
  ('base','ent_link_v','mem_name','eng','Member Name','The name of the person who belongs to the organization'),
  ('base','ent_link_v','org_name','eng','Org Name','The name of the organization or group entity the member belongs to'),
  ('base','ent_link_v','role','eng','Role','The job description or duty of the member with respect to the organization he belongs to'),
  ('base','ent_v','age','eng','Age','Age, in years, of the entity'),
  ('base','ent_v','cas_name','eng','Casual Name','A person''s full name in a casual format: First Last'),
  ('base','ent_v','frm_name','eng','Formal Name','A person''s full name in a formal format: Last, Title First Middle'),
  ('base','ent_v','giv_name','eng','Given Name','A person''s First given name'),
  ('base','ent_v','std_name','eng','Name','The standard format for the entity''s name or, for a person, a standard format: Last, Preferred'),
  ('base','file','crt_by','eng','Created By','The user who entered this record'),
  ('base','file','crt_date','eng','Created','The date this record was created'),
  ('base','file','file_cks','eng','Checksum','A hash or checksum of the data in the document, used to ensure data integrity'),
  ('base','file','file_cmt','eng','Comment','Any other notes about this file'),
  ('base','file','file_data','eng','Data','The binary data contained in this document'),
  ('base','file','file_ent','eng','Entity','The ID number of the entity this file belongs to'),
  ('base','file','file_fmt','eng','Format','A format code to indicate how the data is to be interpreted'),
  ('base','file','file_prim','eng','Primary','If checked this is the primary method of this type for contacting this entity'),
  ('base','file','file_priv','eng','Private','This record should not be shared publicly'),
  ('base','file','file_seq','eng','Sequence','A unique number assigned to each new document for a given entity'),
  ('base','file','file_type','eng','Type','The type of the document'),
  ('base','file','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','file','mod_date','eng','Modified','The date this record was last modified'),
  ('base','file_prim','prim_ent','eng','Entity','The entity ID number of the main file of this type'),
  ('base','file_prim','prim_seq','eng','Sequence','The sequence number of the main file of this type'),
  ('base','file_prim','prim_type','eng','type','The file type this record applies to'),
  ('base','file_v','file_prim','eng','Primary','If true this is the primary file of this type'),
  ('base','file_v','std_name','eng','Entity Name','The name of the entity this file pertains to'),
  ('base','language','code','eng','Language Code','The ISO 3-letter language code.  Where a native T-code exists, it is the one used here.'),
  ('base','language','eng_name','eng','Name in English','The common name of the language English'),
  ('base','language','fra_name','eng','Name in French','The common name of the language in French'),
  ('base','language','iso_2','eng','Code 2','The ISO 2-letter code for this language, if it exists'),
  ('base','language','iso_3b','eng','Biblio Code','The ISO bibliographic 3-letter code for this language'),
  ('base','language_v','columns','eng','Columns','How many database columns are documented in this language'),
  ('base','language_v','messages','eng','Messages','How many UI messages are documented in this language'),
  ('base','language_v','tables','eng','Tables','How many database tables are documented in this language'),
  ('base','language_v','values','eng','Values','How many database column values are documented in this language'),
  ('base','parm','cmt','eng','Comment','Notes you may want to add about why the setting is set to a particular value'),
  ('base','parm','crt_by','eng','Created By','The user who entered this record'),
  ('base','parm','crt_date','eng','Created','The date this record was created'),
  ('base','parm','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','parm','mod_date','eng','Modified','The date this record was last modified'),
  ('base','parm','module','eng','Module','The system or module within the ERP this setting is applicable to'),
  ('base','parm','parm','eng','Name','The name of the parameter setting'),
  ('base','parm','type','eng','Data Type','Indicates the native data type of this paramter (and hence the particular underlying table it will be stored in.)'),
  ('base','parm','v_boolean','eng','Boolean Value','The parameter value in the case when the type is a boolean (true/false) value'),
  ('base','parm','v_date','eng','Date Value','The parameter value in the case when the type is a date'),
  ('base','parm','v_float','eng','Float Value','The parameter value in the case when the type is a real number'),
  ('base','parm','v_int','eng','Integer Value','The parameter value in the case when the type is an integer'),
  ('base','parm','v_text','eng','Text Value','The parameter value in the case when the type is a character string'),
  ('base','parm_audit','a_action','eng','Action','The operation that produced the change (update, delete)'),
  ('base','parm_audit','a_by','eng','Altered By','The username of the user who made the change'),
  ('base','parm_audit','a_date','eng','Date/Time','Date and time of the change'),
  ('base','parm_audit','a_seq','eng','Sequence','A sequential number unique to each alteration'),
  ('base','parm_audit','a_values','eng','Values','JSON object containing the old values of the record before the change'),
  ('base','parm_audit','module','eng','Module','The module name for the parameter that was changed'),
  ('base','parm_audit','parm','eng','Parameter','The parameter name that was changed'),
  ('base','parm_v','value','eng','Value','The value for the parameter setting, expressed as a string'),
  ('base','priv','cmt','eng','Comment','Comments about this privilege allocation to this user'),
  ('base','priv','grantee','eng','Grantee','The username of the entity receiving the privilege'),
  ('base','priv','level','eng','Access Level','What level of access within this privilege.  This is normally null for a group or role privilege or a number from 1 to 3.  1 means limited access, 2 is for normal access, and 3 means supervisory access.'),
  ('base','priv','priv','eng','Privilege','The name of the privilege being granted'),
  ('base','priv','priv_level','eng','Priv Level','Shows the name the privilege level will refer to in the database.  This is formed by joining the privilege name and the level (if present) with an underscore.'),
  ('base','priv_v','priv_list','eng','Priv List','In the case where the privilege refers to a group role, this shows which underlying privileges belong to that role.'),
  ('base','priv_v','std_name','eng','Entity Name','The name of the entity being granted the privilege'),
  ('base','priv_v','username','eng','Username','The username within the database for this entity'),
  ('base','token','allows','eng','Allowed Access','The type of access this token authorizes.  The value "login" grants the user permission to log in.'),
  ('base','token','crt_by','eng','Created By','The user who entered this record'),
  ('base','token','crt_date','eng','Created','The date this record was created'),
  ('base','token','expires','eng','Expires','A time stamp showing when the token will no longer be valid because it has been too long since it was issued'),
  ('base','token','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','token','mod_date','eng','Modified','The date this record was last modified'),
  ('base','token','token','eng','Token','An automatically generated code the user will present to get access'),
  ('base','token','token_ent','eng','Token Entity','The id of the user or entity this token is generated for'),
  ('base','token','token_seq','eng','Entity ID','A sequential number assigned to each new token, unique to the user the tokens are for'),
  ('base','token','used','eng','Used','A time stamp showing when the token was presented back to the system'),
  ('base','token_v','expired','eng','Expired','Indicates that this token is no longer valid because too much time has gone by since it was issued'),
  ('base','token_v','std_name','eng','Name','The standard format for the entity''s name or, for a person, a standard format: Last, Preferred'),
  ('base','token_v','username','eng','Username','The login name of the user this token belongs to'),
  ('base','token_v','valid','eng','Valid','This token can still be used if it has not yet expired and has never yet been used to connect'),
  ('base','token_v_ticket','host','eng','Host','The host name of a computer for the user to connect to using this new ticket'),
  ('base','token_v_ticket','port','eng','Port','The port number the user will to connect to using this new ticket'),
  ('json','cert','chad','eng','CHIP Address','Full JSON CHIP address record for the user'),
  ('json','cert','identity','eng','Identity','JSON MyCHIPs identity record with optional state and birth records'),
  ('json','cert','name','eng','Entity Name','The name of the entity as represented on the CHIP certificate'),
  ('mychips','agents','agent','eng','Agent ID','Unique string identifying the agent service'),
  ('mychips','agents','agent_host','eng','Agent Host Address','The hostname or IP number where peers connect to this agent'),
  ('mychips','agents','agent_ip','eng','Agent IP','The IP number from which this agent last connected'),
  ('mychips','agents','agent_key','eng','Agent Key','The connection public key decoded from the agent ID string'),
  ('mychips','agents','agent_port','eng','Agent Port','The port on which peers connect'),
  ('mychips','agents','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','agents','crt_date','eng','Created','The date this record was created'),
  ('mychips','agents','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','agents','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','chit_tries','ctry_ent','eng','Entity','The entity the chit/tally belongs to'),
  ('mychips','chit_tries','ctry_idx','eng','Index','The index number of this chit'),
  ('mychips','chit_tries','ctry_seq','eng','Sequence','The sequence number of the tally/chit'),
  ('mychips','chit_tries','last','eng','Last Try','The last time we tried'),
  ('mychips','chit_tries','tries','eng','Tries','How many tries we are up to'),
  ('mychips','chits','chain_hash','eng','Chain Hash','A hash of the current chit record, including the previous record''s hash so as to form a hash chain'),
  ('mychips','chits','chain_idx','eng','Chain Index','Chits are stored in a hash-chain to prevent them from being altered later.  This indicates the order of the chit records in the hash chain.'),
  ('mychips','chits','chain_prev','eng','Chain Previous','A copy of the hash from the previous chit in the hash chain'),
  ('mychips','chits','chit_date','eng','Date/Time','The date and time when this transaction is effective'),
  ('mychips','chits','chit_ent','eng','Tally Entity','Entity ID of the owner of the tally this chit belongs to'),
  ('mychips','chits','chit_idx','eng','Chit Index','A unique identifier within the tally, identifying this chit'),
  ('mychips','chits','chit_seq','eng','Tally Sequence','Sequence number of the owner of the tally this chit belongs to'),
  ('mychips','chits','chit_type','eng','Chit Type','The type of transaction represented by this flow of credit'),
  ('mychips','chits','chit_uuid','eng','Chit GUID','A globally unique identifier for this transaction'),
  ('mychips','chits','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','chits','crt_date','eng','Created','The date this record was created'),
  ('mychips','chits','digest','eng','Digest Hash','A hash of the chit transaction that will be digitally signed'),
  ('mychips','chits','issuer','eng','Issuer','Indicates whether the stock holder or the foil holder created (and signed) the chit.  For transaction and lift chits, this indicates which direction value flows (from issuer to recipient).'),
  ('mychips','chits','lift_seq','eng','Lift Sequence','If a chit is part of a lift transaction, this indicates which tally record the chits belong to.  There can be more than one lift record per lift in some cases.'),
  ('mychips','chits','memo','eng','Memo','Any other human-readable text description, context or explanation for the transaction'),
  ('mychips','chits','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','chits','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','chits','reference','eng','Reference','Any arbitrary JSON data about the transaction, meaningful to the parties.  May reference an invoice, a purchase order, a register, other document evidencing goods or services rendered, and a trading relationship between the parties.  For setting chits, this contains the settings being asserted.'),
  ('mychips','chits','request','eng','Request','The state transition algorithm for chits responds to transition requests entered into this field.'),
  ('mychips','chits','signature','eng','Signature','Digital signature of the party authorizing the transaction'),
  ('mychips','chits','status','eng','Status','The status field indicates if the state has progressed to the point where the amount of the chit can be considered pending or final'),
  ('mychips','chits','units','eng','Units','The amount of the transaction, measured in milli-CHIPs (1/1000 of a CHIP)'),
  ('mychips','chits_v','action','eng','Action','Indicates this tally requires some kind of action on the part of the user, such as accepting, rejecting, confirming, etc.'),
  ('mychips','chits_v','clean','eng','Clean','Indicates that the stored hash matches the computed hash.  This is an indication that the record has not been tampered with.'),
  ('mychips','chits_v','digest_v','eng','Computed Digest','A version of the hash digest computed from scratch each time it is fetched (to be compared to the stored version)'),
  ('mychips','chits_v','json','eng','JSON','A JSON representation of the chit transaction, including the digital hash'),
  ('mychips','chits_v','json_core','eng','JSON Core','A JSON representation of the parts of the chit transaction that will be digitally hashed and signed'),
  ('mychips','chits_v','net','eng','Net Value','The chit amount expressed as a positive or negative number, depending on how it accrues to the holder of this half of the tally.'),
  ('mychips','chits_v','net_g','eng','Good Value','The net value of this chit that has been duly signed and so is considered binding.'),
  ('mychips','chits_v','net_p','eng','Pending Value','The net value of this chit that when it has not yet been signed.  A value here indicates it is still pending and not final.'),
  ('mychips','chits_v','state','eng','State','The state is used to track a transaction in process'),
  ('mychips','chits_v_chains','chain_idx','eng','Chain Index','The record number in the chain.  Base tally is -1, first chit is 0, second chit is 1...'),
  ('mychips','chits_v_chains','chain_prev','eng','Prior Hash','Contains the hash of the prior link (chit or tally) in the chain'),
  ('mychips','chits_v_chains','digest','eng','Digest','A SHA256 hash of the MyCHIPs compliant data contained in the individual chit or tally'),
  ('mychips','chits_v_chains','ent','eng','Entity','The entity ID of the owner of the tally the chain belongs to'),
  ('mychips','chits_v_chains','hash_ok','eng','Prior Hashes','Is true if this and all previous records contain an accurate hash of the relevant data in their record'),
  ('mychips','chits_v_chains','last','eng','End of Chain','True if this is the last record in the chain'),
  ('mychips','chits_v_chains','length','eng','Length','Indicates how many chits are part of the chain'),
  ('mychips','chits_v_chains','ok','eng','Chain Valid','True if all hashes are correctly computed up through this record'),
  ('mychips','chits_v_chains','prev_ok','eng','Prior Links','Is true if this and all previous records properly contain the hash copied from the prior record'),
  ('mychips','chits_v_chains','seq','eng','Sequence','The sequence (tally) number of the owner of the tally the chain belongs to'),
  ('mychips','chits_v_chains','uuids','eng','GUID List','Contains a list of all the global IDs for each of the chits (and tally) in the chain'),
  ('mychips','contracts','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','contracts','crt_date','eng','Created','The date this record was created'),
  ('mychips','contracts','digest','eng','Hash','A SHA-256 hash signature of the document (exclusive of this field) which can be referenced by others to prove the accuracy of the contract'),
  ('mychips','contracts','domain','eng','Author Domain','The web domain of the contract''s author (such as gnu.org, fsf.org, mychips.org, etc.)'),
  ('mychips','contracts','language','eng','Language','The standard 3-letter ISO code for the language in which the covenant is expressed'),
  ('mychips','contracts','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','contracts','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','contracts','name','eng','Path Name','A unique name for the contract, which also serves as a URL path, and partial filename such as: mychips/terms/mediation'),
  ('mychips','contracts','published','eng','Published','The date this version of the covenant was first made available to the public'),
  ('mychips','contracts','sections','eng','Sections','Further sub-sections of contract text, describing the terms and conditions of the contract'),
  ('mychips','contracts','tag','eng','Section Tag','A short alphanumeric string which can be used as a target for cross references inside the document'),
  ('mychips','contracts','text','eng','Text','An introductory paragraph of text at the top level of the document'),
  ('mychips','contracts','title','eng','Title','A brief, descriptive title which will be shown as a document or section header when a contract is rendered'),
  ('mychips','contracts','version','eng','Version','The version number, starting at 1, of this contract document'),
  ('mychips','contracts_v','json','eng','JSON','The contract represented in JavaScript Object Notation'),
  ('mychips','contracts_v','source','eng','Source URL','The official web address where the author of this document maintains its public access'),
  ('mychips','lifts','circuit','eng','Circuit User','For circular lifts, this is the bottom local user in our local segment.  It will be the entity to complete the circle.  For linear lifts, this field is null.'),
  ('mychips','lifts','find','eng','Destination','The JSON CHIP Address of the entity we are seeking at the end of the line for this lift.  For circular lifts, it is the foreign peer at the bottom of our local segment.'),
  ('mychips','lifts','life','eng','Lifetime','The amount of time before the lift will be considered expired by its arbiter referee'),
  ('mychips','lifts','lift_date','eng','Lift Date','The date/time the lift was originated'),
  ('mychips','lifts','lift_seq','eng','Lift Sequence','A lift can cross a single database multiple times.  This will increment for each new lift record created as this happens.'),
  ('mychips','lifts','lift_type','eng','Lift Type','Whether/how this lift record was originated'),
  ('mychips','lifts','lift_uuid','eng','Lift GUID','A globally unique identifier for this lift.  It will be the same id across all servers who participate in the same transaction.'),
  ('mychips','lifts','origin','eng','Origin','A JSON record describing information about how/where the lift originated.  Some parts encrypted for eyes of the destination agent only.'),
  ('mychips','lifts','referee','eng','Referee','The JSON CHIP Address of the site who will decide when the lift has expired'),
  ('mychips','lifts','request','eng','Request','The state transition algorithm for lifts responds to transition requests entered into this field.'),
  ('mychips','lifts','signature','eng','Signature','Digital signature of the lift originator indicating that the transaction is binding.'),
  ('mychips','lifts','status','eng','Status','The status field indicates what has been done and what needs to happen next, if anything'),
  ('mychips','lifts','tallies','eng','Tallies','An array of the tally global ID''s in between the users/peers in our local segment path'),
  ('mychips','lifts','units','eng','Units','The amount of the lift transaction, as measured in milli-CHIPs (1/1,000)'),
  ('mychips','lifts_v','circular','eng','Circular','The lift is intended to form a complete circuit'),
  ('mychips','lifts_v','clean','eng','Clean','Indicates that the stored hash matches the computed hash.  This is an indication that the lift record has not been tampered with.'),
  ('mychips','lifts_v','digest_v','eng','Computed Digest','A version of the hash digest computed from scratch each time it is fetched (to be compared to the stored version)'),
  ('mychips','lifts_v','expires','eng','Expires','The date/time when the lift will be considered expired by the referee'),
  ('mychips','lifts_v','json','eng','JSON','A JSON representation of the lift transaction, including the digital hash'),
  ('mychips','lifts_v','json_core','eng','JSON Core','A JSON representation of the parts of the lift transaction that will be digitally hashed and signed'),
  ('mychips','lifts_v','remains','eng','Remains','The amount of time before expiration, the local lift record was created and then relayed along'),
  ('mychips','lifts_v','state','eng','State','Derived from the status and request columns to show current transition state'),
  ('mychips','lifts_v_dist','bot_chad','eng','Bottom Address','CHIP address of the entity who owns the bottom (input) tally in the local segment for this lift'),
  ('mychips','lifts_v_dist','bot_tally','eng','Bottom Tally','Uuid of the bottom (input) tally in the local segment for this lift'),
  ('mychips','lifts_v_dist','find_v','eng','Find Template','A default template for the destination property for a new lift'),
  ('mychips','lifts_v_dist','origin_v','eng','Origin Template','A default template for the origin property for a new lift'),
  ('mychips','lifts_v_dist','referee_v','eng','Referee Template','A default template for the referee property for a new lift'),
  ('mychips','lifts_v_dist','top_chad','eng','Top Address','CHIP address of the entity who owns the top (output) tally in the local segment for this lift'),
  ('mychips','lifts_v_dist','top_tally','eng','Top Tally','Uuid of the top (output) tally in the local segment for this lift'),
  ('mychips','route_tries','last','eng','Last Try','The last time we tried'),
  ('mychips','route_tries','rtry_rid','eng','Retry Route ID','Primary key of the route we are tracking retries for'),
  ('mychips','route_tries','tries','eng','Tries','How many tries we are up to'),
  ('mychips','routes','dst_agent','eng','Destination Agent','The agent address for the entity this route leads to'),
  ('mychips','routes','dst_cid','eng','Destination CHIP ID','The CHIP identifier for the entity this route leads to'),
  ('mychips','routes','good_date','eng','Date Found','The date/time this path was last marked as good by an upstream foreign server'),
  ('mychips','routes','lift_count','eng','Use Count','A counter that is incremented each time this path is used in a lift'),
  ('mychips','routes','lift_date','eng','Last Used','The date/time this path was last used in a lift'),
  ('mychips','routes','margin','eng','Lift Margin','The fee ratio we can expect to move any lift transaction along this route'),
  ('mychips','routes','max','eng','Lift Maximum','The most we can expect to lift along this route, which might incur an extra transaction fee'),
  ('mychips','routes','min','eng','Lift Minimum','The most we can expect to lift along this route without pushing foils past their target setting'),
  ('mychips','routes','req_ent','eng','Requester','The ID of the local entity through which this route request originated (also where to return query results to)'),
  ('mychips','routes','req_tseq','eng','Requester Tally','The sequence number of the tally the route request came over (leave null for local queries)'),
  ('mychips','routes','reward','eng','Lift Reward','An additional fee ratio we can expect to move lifts beyond the Lift Minimum amount'),
  ('mychips','routes','rid','eng','Route ID','A unique integer assigned by the system to identify each route record'),
  ('mychips','routes','status','eng','Status','Indicates whether this route is useable or if not, what progress is being made to discover such a route'),
  ('mychips','routes','step','eng','Step','How many steps we are along the way from where this route request was originated'),
  ('mychips','routes','via_ent','eng','Route Entity','The ID of a local entity who owns the tally this route starts on'),
  ('mychips','routes','via_tseq','eng','Route Tally','Sequence number of the tally this route begins on'),
  ('mychips','routes_v','dst_chad','eng','Destination Address','Full JSON CHIP address for the entity the route is searching for'),
  ('mychips','routes_v','expired','eng','Expired','This route is uncertain because of the amount time passed since it was affirmed'),
  ('mychips','routes_v','expires','eng','Expires','When this route will be considered uncertain'),
  ('mychips','routes_v','json','eng','Route Object','JSON representation of the route used in peer-to-peer messages'),
  ('mychips','routes_v','lading','eng','Lading','A JSON structure describing how much value can be lifted along this route and what fees might apply'),
  ('mychips','routes_v','last','eng','Last Try','When was the last retry done'),
  ('mychips','routes_v','native','eng','Native','The entity requesting the route is a local user'),
  ('mychips','routes_v','req_agent','eng','Request Agent','Agent address for the owner of the tally the route is requested through'),
  ('mychips','routes_v','req_chad','eng','Request Address','Full JSON CHIP address for the owner of the tally the route is requested through'),
  ('mychips','routes_v','req_cid','eng','Request CHIP ID','CHIP ID of the owner of the tally the route is requested through'),
  ('mychips','routes_v','req_tally','eng','Request Tally','ID of the tally the route is requested through (or null for local requests)'),
  ('mychips','routes_v','rpt_agent','eng','Req Partner Agent','Agent address for the foreign partner on the tally the route is requested through'),
  ('mychips','routes_v','rpt_chad','eng','Req Partner Address','Full JSON CHIP address for the foreign partner on the tally the route is requested through'),
  ('mychips','routes_v','rpt_cid','eng','Req Partner CHIP ID','CHIP ID of the foreign partner on the tally the route is requested through'),
  ('mychips','routes_v','sorter','eng','Priority Sort','A field used to prioritize routes and potential routes for being generated/retried'),
  ('mychips','routes_v','state','eng','State','Indicates how/whether this route might be useable'),
  ('mychips','routes_v','tries','eng','Tries','How many times has this route request tried without connecting to the intended peer'),
  ('mychips','routes_v','via_agent','eng','Route Via Agent','Agent address for the owner of the tally the route starts on'),
  ('mychips','routes_v','via_chad','eng','Route Via Address','Full JSON CHIP address for the owner of the tally the route starts on'),
  ('mychips','routes_v','via_cid','eng','Route Via CHIP ID','CHIP ID of the owner of the tally the route starts on'),
  ('mychips','routes_v','via_tally','eng','Route Via Tally','ID of the tally the route starts on'),
  ('mychips','routes_v','vip_agent','eng','Route Partner Agent','Agent address for the foreign partner on the tally the route starts on'),
  ('mychips','routes_v','vip_chad','eng','Route Partner Address','Full JSON CHIP address for the foreign partner on the tally the route starts on'),
  ('mychips','routes_v','vip_cid','eng','Route Partner CHIP ID','CHIP ID of the foreign partner on the tally the route starts on'),
  ('mychips','tallies','_last_chit','eng','Last Chit','Used internally to create new chit record index numbers'),
  ('mychips','tallies','bound','eng','Trade Limit','The maximum amount of value the stock/foil owner is willing to accumulate on this tally'),
  ('mychips','tallies','chain_conf','eng','Chain Confirmed','The index of the last chit in the chain that has been confirmed with the partner peer'),
  ('mychips','tallies','clutch','eng','Sell Margin','A cost associated with a lift/drop through this tally, which would result in a loss of value for the holder.  Zero means no cost.  A value of 1 will effectively prevent further trading in that direction.'),
  ('mychips','tallies','comment','eng','Comment','Any notes the user might want to enter regarding this tally'),
  ('mychips','tallies','contract','eng','Contract','The hash ID of the standard contract this tally is based upon.'),
  ('mychips','tallies','cr_limit','eng','Credit Limit','The maximum amount the Client (Foil) is granted to borrow from the Vendor (Stock) in exchange for goods and services'),
  ('mychips','tallies','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','tallies','crt_date','eng','Created','The date this record was created'),
  ('mychips','tallies','digest','eng','Digest Hash','A digitally encrypted hash indicating a unique but condensed representation of the critical information belonging to the tally.  The originator will sign this hash to make the lift binding.'),
  ('mychips','tallies','dr_limit','eng','Debit Limit','The maximum amount the Vendor (Stock) is granted to borrow from the Client (Foil) in exchange for goods and services'),
  ('mychips','tallies','foil_terms','eng','Foilee Terms','The credit terms by which the holder of the tally foil is governed'),
  ('mychips','tallies','hold_agent','eng','Holder Agent','Cached value of holder''s agent from the holder certificate'),
  ('mychips','tallies','hold_cert','eng','Holder Certificate','The JSON structure of identifying data for the entity that owns/holds this tally'),
  ('mychips','tallies','hold_cid','eng','Holder CHIP ID','Cached value of holder''s CHIP identity from the holder certificate'),
  ('mychips','tallies','hold_sig','eng','Holder Signed','The digital signature of the entity that owns/holds this tally'),
  ('mychips','tallies','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','tallies','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','tallies','part_agent','eng','Partner Agent','Cached value of partner''s agent from the holder certificate'),
  ('mychips','tallies','part_cert','eng','Partner Certificate','The JSON structure of identifying data for the other party to this tally'),
  ('mychips','tallies','part_cid','eng','Partner CHIP ID','Cached value of partner''s CHIP identify from the holder certificate'),
  ('mychips','tallies','part_ent','eng','Partner Entity','The entity id number of the other party to this tally'),
  ('mychips','tallies','part_sig','eng','Partner Signed','The digital signature of the other party to this tally'),
  ('mychips','tallies','request','eng','Request','Requested next status for the tally'),
  ('mychips','tallies','reward','eng','Buy Margin','A cost associated with a lift/drop through this tally, which would result in an accumulation of value for the holder in excess of the target value.  Zero means no cost.  A positive percentage indicates a cost, or disincentive to trade.  For example, 0.01 means a 1% cost for doing a lift.  A negative number means the tally owner will give up some value in order to get lifts/drops done.'),
  ('mychips','tallies','status','eng','Status','Current status of the tally record'),
  ('mychips','tallies','stock_terms','eng','Stockee Terms','The credit terms by which the holder of the tally stock is governed'),
  ('mychips','tallies','tally_date','eng','Tally Date','The date and time this tally was initiated between the parties'),
  ('mychips','tallies','tally_ent','eng','Tally Entity','The ID number of the entity or person this tally belongs to'),
  ('mychips','tallies','tally_seq','eng','Tally Sequence','A unique number among all tallies owned by this entity'),
  ('mychips','tallies','tally_type','eng','Tally Type','Determines if this entity is typically the creditor (stock) or the debtor (foil) for this tally'),
  ('mychips','tallies','tally_uuid','eng','Tally GUID','A globally unique identifier for this tally'),
  ('mychips','tallies','target','eng','Target Balance','The ideal total of units the lift administrator should attempt to accumulate when conducting lifts.  Lifts/drops beyond this value may be subject to margin costs.'),
  ('mychips','tallies','units_c','eng','Units Good','Net milliCHIPs committed on this tally (cached copy)'),
  ('mychips','tallies','units_pc','eng','Units Pending','Net milliCHIPs committed on this tally if/when current pending transactions have all settled (cached copy)'),
  ('mychips','tallies','version','eng','Version','A number indicating the format standard this tally adheres to'),
  ('mychips','tallies_v','action','eng','Action','Indicates this tally requires some kind of action on the part of the user, such as accepting, rejecting, confirming, etc.'),
  ('mychips','tallies_v','chits','eng','Chits','The total number of chit transactions recorded on the tally'),
  ('mychips','tallies_v','clean','eng','Clean','Indicates that the stored hash matches the computed hash.  This is an indication that the tally has not been tampered with.'),
  ('mychips','tallies_v','digest_v','eng','Computed Digest','A version of the hash digest computed from scratch each time it is fetched (to be compared to the stored version)'),
  ('mychips','tallies_v','hold_addr','eng','Holder Address','The CHIP address (cid:agent) of the owner of the tally'),
  ('mychips','tallies_v','hold_chid','eng','Holder CHIP Address','Full JSON CHIP address of the entity that owns this part of the tally'),
  ('mychips','tallies_v','inside','eng','Inside','The partner entity is also hosted by the same system as the tally owner'),
  ('mychips','tallies_v','json','eng','JSON','A JSON representation of the tally, including the digital hash'),
  ('mychips','tallies_v','json_core','eng','JSON Core','A JSON representation of the parts of the tally that will be digitally hashed and signed'),
  ('mychips','tallies_v','latest','eng','Last Chit','The date of the latest chit on the tally'),
  ('mychips','tallies_v','liftable','eng','Liftable','Indicates if the tally is eligible to participate in lifts'),
  ('mychips','tallies_v','net','eng','Signed Units','Total milliCHIP value on the tally, as summed from current chits'),
  ('mychips','tallies_v','net_c','eng','Signed Good Units','Total milliCHIP value of committed chits'),
  ('mychips','tallies_v','net_pc','eng','Signed Pending','Total milliSHIP value of committed and pending chits'),
  ('mychips','tallies_v','part_addr','eng','Partner Address','The CHIP address (cid:agent) of the partner on this tally'),
  ('mychips','tallies_v','part_chid','eng','Partner CHIP Address','Full JSON CHIP address of the partner entity on the other end of the tally'),
  ('mychips','tallies_v','policy','eng','Policy','A JSON record of the standard lift and drop parameters'),
  ('mychips','tallies_v','state','eng','State','A computed value indicating the state of progress as the tally goes through its lifecycle'),
  ('mychips','tallies_v_net','inp','eng','Input Node ID','The local ID (or null if foreign peer) of the node who will give value in the lift'),
  ('mychips','tallies_v_net','inv','eng','Inverted','True if the link is a tally with a foreign peer and it is being considered for a drop (reverse lift)'),
  ('mychips','tallies_v_net','margin','eng','Lift Margin','The fee ratio we can expect to move any lift transaction along this link'),
  ('mychips','tallies_v_net','max','eng','Maximum Lift','Maximum number of units possible to lift on this link with possible costs applicable'),
  ('mychips','tallies_v_net','min','eng','Minimum Lift','Minimum number of units possible to lift on this link without reward cost applicable'),
  ('mychips','tallies_v_net','out','eng','Output Node ID','The local ID (or null if foreign peer) of the node who will receive value in the lift'),
  ('mychips','tallies_v_net','part','eng','Partner ID','Local ID (or null if foreign peer) of the partner entity'),
  ('mychips','tallies_v_net','sign','eng','Link Sign','Whether will accrue positive or negative on this tally (based on stock or foil)'),
  ('mychips','tallies_v_net','type','eng','Tally Type','Type (stock or foil) of the tally for this link'),
  ('mychips','tallies_v_net','uuid','eng','Tally UUID','Unique Id of the tally associated with this link'),
  ('mychips','tallies_v_paths','at','eng','User ID Internal','An array of the user IDs in this pathway not including the input or output node'),
  ('mychips','tallies_v_paths','ath','eng','User IDs -First','An array of the user IDs in this pathway not including the input node'),
  ('mychips','tallies_v_paths','bang','eng','Lift Benefit','The product of the pathway length, and the minimum liftable units.  This gives an idea of the relative benefit of conducting a lift along this pathway.'),
  ('mychips','tallies_v_paths','bot','eng','Bottom User ID','ID of the local user who owns the tally that is the beginning (input) link of the pathway'),
  ('mychips','tallies_v_paths','bot_agent','eng','Bottom User Agent','CHIP Agent address of the local user who owns the tally this lift pathway starts with'),
  ('mychips','tallies_v_paths','bot_chad','eng','Bottom User CHAD','Full CHIP address of the local user who owns the tally this lift pathway starts with'),
  ('mychips','tallies_v_paths','bot_cid','eng','Bottom User CID','CHIP ID of the local user who owns the tally this lift pathway starts with'),
  ('mychips','tallies_v_paths','bot_tseq','eng','Bottom Tally Seq','The sequence number of the tally at the beginning (input) of this pathway'),
  ('mychips','tallies_v_paths','bot_uuid','eng','Bottom Tally ID','The identifier of the tally at the beginning (input) of this pathway'),
  ('mychips','tallies_v_paths','circuit','eng','Circuit','A flag indicating that the pathway forms a loop from end to end'),
  ('mychips','tallies_v_paths','edges','eng','Node Length','The number of peer nodes in this pathway'),
  ('mychips','tallies_v_paths','fori','eng','Input Foreign','True if the first node in the path is not a user on the local system'),
  ('mychips','tallies_v_paths','foro','eng','Output Foreign','True if the last node in the path is not a user on the local system'),
  ('mychips','tallies_v_paths','inp','eng','Path Start ID','Entity ID of the user (or null if a foreign peer) this lift pathway starts with'),
  ('mychips','tallies_v_paths','inp_agent','eng','Path Input Agent','CHIP Agent address of the entity this lift pathway starts with'),
  ('mychips','tallies_v_paths','inp_chad','eng','Path Input CHAD','Full CHIP address of the entity this lift pathway starts with'),
  ('mychips','tallies_v_paths','inp_cid','eng','Path Input CID','CHIP ID of the entity this lift pathway starts with'),
  ('mychips','tallies_v_paths','nodes','eng','Edge Length','The number of links between nodes in this pathway'),
  ('mychips','tallies_v_paths','out','eng','Path End ID','Entity ID of the user (or null if a foriegn peer) this lift pathway ends with'),
  ('mychips','tallies_v_paths','out_agent','eng','Path Output Agent','CHIP Agent address of the entity this lift pathway ends with'),
  ('mychips','tallies_v_paths','out_chad','eng','Path Output CHAD','Full CHIP address of the entity this lift pathway ends with'),
  ('mychips','tallies_v_paths','out_cid','eng','Path Output CID','CHIP ID of the entity this lift pathway ends with'),
  ('mychips','tallies_v_paths','pat','eng','User ID -Last','An array of the user IDs in this pathway not including the output node'),
  ('mychips','tallies_v_paths','path','eng','User ID List','An array of the user IDs in this pathway'),
  ('mychips','tallies_v_paths','segment','eng','Lift Segment','The input and output nodes in the pathway are both foreign entities'),
  ('mychips','tallies_v_paths','signs','eng','Tally Sign List','An array of the signs (+/- = lift/drop) in this pathway'),
  ('mychips','tallies_v_paths','top','eng','Top User ID','ID of the local user who owns the tally that is the ending (output) link of the pathway'),
  ('mychips','tallies_v_paths','top_agent','eng','Top User Agent','CHIP Agent address of the local user who owns the tally this lift pathway ends with'),
  ('mychips','tallies_v_paths','top_chad','eng','Top User CHAD','Full CHIP address of the local user who owns the tally this lift pathway ends with'),
  ('mychips','tallies_v_paths','top_cid','eng','Top User CID','CHIP ID of the local user who owns the tally this lift pathway ends with'),
  ('mychips','tallies_v_paths','top_tseq','eng','Top Tally Seq','The sequence number of the tally at the end (output) of this pathway'),
  ('mychips','tallies_v_paths','top_uuid','eng','Top Tally ID','The identifier of the tally at the end (output) of this pathway'),
  ('mychips','tallies_v_paths','uuids','eng','Tally ID List','An array of the tally identifiers in this pathway'),
  ('mychips','tally_tries','last','eng','Last Tried','When the last attempt was made to process state changes on this tally'),
  ('mychips','tally_tries','tries','eng','Retries','How many times the peer server has attempted to act on the state request for this tally'),
  ('mychips','tally_tries','ttry_ent','eng','Tally Entity','The entity that owns the tally'),
  ('mychips','tally_tries','ttry_seq','eng','Tally Sequence','The unique sequence number of the tally'),
  ('mychips','tokens','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','tokens','crt_date','eng','Created','The date this record was created'),
  ('mychips','tokens','expires','eng','Expires','Indicates when the token is no longer valid'),
  ('mychips','tokens','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','tokens','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','tokens','reuse','eng','Reusable','Can issue multiple tallies from a single token'),
  ('mychips','tokens','tally_seq','eng','Tally Sequence','An index indicating which tally will be issued in connection with this token'),
  ('mychips','tokens','token','eng','Token','The digital code of the token'),
  ('mychips','tokens','token_ent','eng','Token Entity','Entity ID of the this token is issued for'),
  ('mychips','tokens','token_seq','eng','Token Sequence','Keeps count of the various tokens created for this entity'),
  ('mychips','tokens','used','eng','Used','Indicates true once the token has been used'),
  ('mychips','users','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','users','crt_date','eng','Created','The date this record was created'),
  ('mychips','users','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','users','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','users','peer_agent','eng','Peer Agent','The agent address where traffic is handled for this user'),
  ('mychips','users','peer_cid','eng','CHIP ID','An ID string or name, unique to this user on its own CHIP service provider''s system.  Similar to the name portion of an email address: <CHIP_ID>@<Provider_host_or_IP>'),
  ('mychips','users','peer_named','eng','Birth Name','The peer''s name at birth, used in the certificate identity record'),
  ('mychips','users','peer_psig','eng','Peer Public Key','The peer''s public key, known to other trading partners and used for signing transactions'),
  ('mychips','users','user_cmt','eng','User Comments','Administrative comments about this user'),
  ('mychips','users','user_ent','eng','User Entity','A link to the entities base table'),
  ('mychips','users','user_ent','fin','Entiteettien linkki','Yhteys yhteisön peruspöytään'),
  ('mychips','users','user_hid','eng','Hashed ID','An obscured version of the ID by which might be given out as a more anonymous destination for a transaction'),
  ('mychips','users','user_host','eng','User Host Address','The hostname or IP number where the users''s mobile application connects'),
  ('mychips','users','user_port','eng','User Port','The port to which the user''s mobile device will connect'),
  ('mychips','users','user_stat','eng','Trading Status','The current state of the user''s account for trading of CHIPs'),
  ('mychips','users','user_stat','fin','Kaupan tila','CHIP-tilin kaupankäynnin tilille'),
  ('mychips','users_v','mobi_socket','fin','Käyttäjä pistorasia','IP-numero ja portti, johon käyttäjän mobiililaite yhdistää'),
  ('mychips','users_v','peer_sock','eng','Peer Socket','The IP Number, and port where other servers can connect to trade with this peer.'),
  ('mychips','users_v','user_sock','eng','User Socket','The IP Number, and port to which the user''s mobile device will connect'),
  ('mychips','users_v_tallies','x','eng','X',''),
  ('wm','column_ambig','col','eng','Column','The name of the column within the view'),
  ('wm','column_ambig','count','eng','Count','The number of possible native tables for this column'),
  ('wm','column_ambig','natives','eng','Natives','A list of the possible native tables for this column'),
  ('wm','column_ambig','sch','eng','Schema','The name of the schema this view is in'),
  ('wm','column_ambig','spec','eng','Specified','True if the definitive native table has been specified explicitly in the schema definition files'),
  ('wm','column_ambig','tab','eng','Table','The name of the view'),
  ('wm','column_data','cdt_col','eng','Column Name','The name of the column whose data is being described'),
  ('wm','column_data','cdt_sch','eng','Schema Name','The schema of the table this column belongs to'),
  ('wm','column_data','cdt_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','column_data','def','eng','Default','Default value for this column if none is explicitly assigned'),
  ('wm','column_data','field','eng','Field','The number of the column as it appears in the table'),
  ('wm','column_data','is_pkey','eng','Def Prim Key','Indicates that this column is defined as a primary key in the database (can be overridden by a wyseman setting)'),
  ('wm','column_data','length','eng','Length','The normal number of characters this item would occupy'),
  ('wm','column_data','nonull','eng','Not Null','Indicates that the column is not allowed to contain a null value'),
  ('wm','column_data','tab_kind','eng','Table/View','The kind of database relation this column is in (r=table, v=view)'),
  ('wm','column_data','type','eng','Data Type','The kind of data this column holds, such as integer, string, date, etc.'),
  ('wm','column_def','val','eng','Init Value','An expression used for default initialization'),
  ('wm','column_istyle','cs_obj','eng','Object Name','The schema and table name this style applies to'),
  ('wm','column_istyle','cs_value','eng','Given Style','The style, specified explicitly for this object'),
  ('wm','column_istyle','nat_value','eng','Native Style','The inherited style as specified by an ancestor object'),
  ('wm','column_lang','col','eng','Column','The name of the column the metadata applies to'),
  ('wm','column_lang','nat','eng','Native','The (possibly ancestor) schema and table/view this language information descends from'),
  ('wm','column_lang','obj','eng','Object','The schema name and the table/view name'),
  ('wm','column_lang','sch','eng','Schema','The schema that holds the table or view this language data applies to'),
  ('wm','column_lang','system','eng','System','Indicates if this table/view is built in to PostgreSQL'),
  ('wm','column_lang','tab','eng','Table','The table or view this language data applies to'),
  ('wm','column_lang','values','eng','Values','A JSON description of the allowable values for this column'),
  ('wm','column_meta','col','eng','Column','The name of the column the metadata applies to'),
  ('wm','column_meta','nat','eng','Native','The (possibly ancestor) schema and table/view this metadata descends from'),
  ('wm','column_meta','obj','eng','Object','The schema name and the table/view name'),
  ('wm','column_meta','sch','eng','Schema','The schema that holds the table or view this metadata applies to'),
  ('wm','column_meta','styles','eng','Styles','An array of default display styles for this column'),
  ('wm','column_meta','tab','eng','Table','The table or view this metadata applies to'),
  ('wm','column_meta','values','eng','Values','An array of allowable values for this column'),
  ('wm','column_native','cnt_col','eng','Column Name','The name of the column whose native source is being described'),
  ('wm','column_native','cnt_sch','eng','Schema Name','The schema of the table this column belongs to'),
  ('wm','column_native','cnt_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','column_native','nat_col','eng','Column Name','The name of the column in the native table from which the higher level column derives'),
  ('wm','column_native','nat_exp','eng','Explic Native','The information about the native table in this record has been defined explicitly in the schema description (not derived from the database system catalogs)'),
  ('wm','column_native','nat_sch','eng','Schema Name','The schema of the native table the column derives from'),
  ('wm','column_native','nat_tab','eng','Table Name','The name of the table the column natively derives from'),
  ('wm','column_native','pkey','eng','Primary Key','Wyseman can often determine the "primary key" for views on its own from the database.  When it can''t, you have to define it explicitly in the schema.  This indicates that thiscolumn should be regarded as a primary key field when querying the view.'),
  ('wm','column_pub','col','eng','Column Name','The name of the column being described'),
  ('wm','column_pub','help','eng','Description','A longer description of what the table is used for'),
  ('wm','column_pub','language','eng','Language','The language of the included textual descriptions'),
  ('wm','column_pub','nat','eng','Native Object','The name of the native table, prefixed by the native schema'),
  ('wm','column_pub','obj','eng','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','column_pub','sch','eng','Schema Name','The schema of the table the column belongs to'),
  ('wm','column_pub','tab','eng','Table Name','The name of the table that holds the column being described'),
  ('wm','column_pub','title','eng','Title','A short title for the table'),
  ('wm','column_style','cs_col','eng','Column Name','The name of the column this style pertains to'),
  ('wm','column_style','cs_sch','eng','Schema Name','The schema for the table this style pertains to'),
  ('wm','column_style','cs_tab','eng','Table Name','The name of the table containing the column this style pertains to'),
  ('wm','column_style','sw_name','eng','Name','The name of the style being described'),
  ('wm','column_style','sw_value','eng','Value','The value for this particular style'),
  ('wm','column_text','ct_col','eng','Column Name','The name of the column being described'),
  ('wm','column_text','ct_sch','eng','Schema Name','The schema this column''s table belongs to'),
  ('wm','column_text','ct_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','column_text','help','eng','Description','A longer description of what the column is used for'),
  ('wm','column_text','language','eng','Language','The language this description is in'),
  ('wm','column_text','title','eng','Title','A short title for the column'),
  ('wm','fkey_data','conname','eng','Constraint','The name of the the foreign key constraint in the database'),
  ('wm','fkey_data','key','eng','Key','The number of which field of a compound key this record describes'),
  ('wm','fkey_data','keys','eng','Keys','The total number of columns used for this foreign key'),
  ('wm','fkey_data','kyf_col','eng','Foreign Columns','The name of the columns in the referenced table''s key'),
  ('wm','fkey_data','kyf_field','eng','Foreign Field','The number of the column in the referenced table''s key'),
  ('wm','fkey_data','kyf_sch','eng','Foreign Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkey_data','kyf_tab','eng','Foreign Table','The name of the table that is referenced by the key fields'),
  ('wm','fkey_data','kyt_col','eng','Base Columns','The name of the column in the referencing table''s key'),
  ('wm','fkey_data','kyt_field','eng','Base Field','The number of the column in the referencing table''s key'),
  ('wm','fkey_data','kyt_sch','eng','Base Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkey_data','kyt_tab','eng','Base Table','The name of the table that has the referencing key fields'),
  ('wm','fkey_pub','fn_col','eng','For Nat Column','The name of the column in the native referenced by the key component'),
  ('wm','fkey_pub','fn_obj','eng','For Nat Object','Concatenated schema.table for the native table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_sch','eng','For Nat Schema','The schema of the native table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_tab','eng','For Nat Table','The name of the native table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_col','eng','For Column','The name of the column referenced by the key component'),
  ('wm','fkey_pub','ft_obj','eng','For Object','Concatenated schema.table for the table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_sch','eng','For Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_tab','eng','For Table','The name of the table that is referenced by the key fields'),
  ('wm','fkey_pub','tn_col','eng','Nat Column','The name of the column in the native referencing table''s key component'),
  ('wm','fkey_pub','tn_obj','eng','Nat Object','Concatenated schema.table for the native table that has the referencing key fields'),
  ('wm','fkey_pub','tn_sch','eng','Nat Schema','The schema of the native table that has the referencing key fields'),
  ('wm','fkey_pub','tn_tab','eng','Nat Table','The name of the native table that has the referencing key fields'),
  ('wm','fkey_pub','tt_col','eng','Column','The name of the column in the referencing table''s key component'),
  ('wm','fkey_pub','tt_obj','eng','Object','Concatenated schema.table that has the referencing key fields'),
  ('wm','fkey_pub','tt_sch','eng','Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkey_pub','tt_tab','eng','Table','The name of the table that has the referencing key fields'),
  ('wm','fkey_pub','unikey','eng','Unikey','Used to differentiate between multiple fkeys pointing to the same destination, and multi-field fkeys pointing to multi-field destinations'),
  ('wm','fkeys_data','conname','eng','Constraint','The name of the the foreign key constraint in the database'),
  ('wm','fkeys_data','ksf_cols','eng','Foreign Columns','The name of the columns in the referenced table''s key'),
  ('wm','fkeys_data','ksf_sch','eng','Foreign Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkeys_data','ksf_tab','eng','Foreign Table','The name of the table that is referenced by the key fields'),
  ('wm','fkeys_data','kst_cols','eng','Base Columns','The name of the columns in the referencing table''s key'),
  ('wm','fkeys_data','kst_sch','eng','Base Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkeys_data','kst_tab','eng','Base Table','The name of the table that has the referencing key fields'),
  ('wm','fkeys_pub','fn_cols','eng','For Nat Columns','The name of the columns in the native referenced by the key'),
  ('wm','fkeys_pub','fn_obj','eng','For Nat Object','Concatenated schema.table for the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_sch','eng','For Nat Schema','The schema of the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_tab','eng','For Nat Table','The name of the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_cols','eng','For Columns','The name of the columns referenced by the key'),
  ('wm','fkeys_pub','ft_obj','eng','For Object','Concatenated schema.table for the table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_sch','eng','For Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_tab','eng','For Table','The name of the table that is referenced by the key fields'),
  ('wm','fkeys_pub','tn_cols','eng','Nat Columns','The name of the columns in the native referencing table''s key'),
  ('wm','fkeys_pub','tn_obj','eng','Nat Object','Concatenated schema.table for the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_sch','eng','Nat Schema','The schema of the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_tab','eng','Nat Table','The name of the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_cols','eng','Columns','The name of the columns in the referencing table''s key'),
  ('wm','fkeys_pub','tt_obj','eng','Object','Concatenated schema.table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_sch','eng','Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_tab','eng','Table','The name of the table that has the referencing key fields'),
  ('wm','message_text','code','eng','Code','A unique code referenced in the source code to evoke this message in the language of choice'),
  ('wm','message_text','help','eng','Description','A longer, more descriptive version of the message'),
  ('wm','message_text','language','eng','Language','The language this message is in'),
  ('wm','message_text','mt_sch','eng','Schema Name','The schema of the table this message belongs to'),
  ('wm','message_text','mt_tab','eng','Table Name','The name of the table this message belongs to is in'),
  ('wm','message_text','title','eng','Title','A short version for the message, or its alert'),
  ('wm','objects','build','eng','Build','The object needs to be rebuilt according to an updated spec'),
  ('wm','objects','built','eng','Built','The object represented by this record is built and current according to this create script'),
  ('wm','objects','checkit','eng','Check','This record needs to have its dependencies and consistency checked'),
  ('wm','objects','col_data','eng','Display','Switches found, expressing preferred display characteristics for columns, assuming this is a view or table object'),
  ('wm','objects','crt_date','eng','Created','When this object record was first created'),
  ('wm','objects','crt_sql','eng','Create','The SQL code to build this object'),
  ('wm','objects','del_idx','eng','Delta Index','Points to the next migration command that has not yet been deployed'),
  ('wm','objects','delta','eng','Deltas','JSON list of table alteration commands used when migrating from one table version to the next'),
  ('wm','objects','deps','eng','Depends','A list of un-expanded dependencies for this object, exactly as expressed in the source file'),
  ('wm','objects','drp_sql','eng','Drop','The SQL code to drop this object'),
  ('wm','objects','grants','eng','Grants','The permission grants found, applicable to this object'),
  ('wm','objects','max_rel','eng','Maximum','The latest release this version of this object belongs to'),
  ('wm','objects','min_rel','eng','Minimum','The oldest release this version of this object belongs to'),
  ('wm','objects','mod_date','eng','Modified','When this object record was last modified'),
  ('wm','objects','module','eng','Module','The name of a code module (package) this object belongs to'),
  ('wm','objects','ndeps','eng','Normal Deps','An expanded and normalized array of dependencies, guaranteed to exist in another record of the table'),
  ('wm','objects','obj_nam','eng','Name','The schema and name of object as known within that schema'),
  ('wm','objects','obj_typ','eng','Type','The object type, for example: table, function, trigger, etc.'),
  ('wm','objects','obj_ver','eng','Version','A sequential integer showing how many times this object has been modified, as a part of an official release.  Changes to the current (working) release do not increment this number.'),
  ('wm','objects_v','object','eng','Object','Full type and name of this object'),
  ('wm','objects_v','release','eng','Release','A release this version of the object belongs to'),
  ('wm','objects_v_dep','cycle','eng','Cycle','Prevents the recursive view gets into an infinite loop'),
  ('wm','objects_v_dep','depend','eng','Depends On','Another object that must be created before this object'),
  ('wm','objects_v_dep','depth','eng','Depth','The depth of the dependency tree, when following this particular dependency back to the root.'),
  ('wm','objects_v_dep','fpath','eng','Full Path','The full path of the dependency tree above this object (including this object).'),
  ('wm','objects_v_dep','object','eng','Object','Full object type and name (type:name)'),
  ('wm','objects_v_dep','od_nam','eng','Name','Schema and name of object as known within that schema'),
  ('wm','objects_v_dep','od_release','eng','Release','The release this object belongs to'),
  ('wm','objects_v_dep','od_typ','eng','Type','Function, view, table, etc'),
  ('wm','objects_v_dep','path','eng','Path','The path of the dependency tree above this object'),
  ('wm','objects_v_depth','depth','eng','Max Depth','The maximum depth of this object along any path in the dependency tree'),
  ('wm','releases','committed','eng','Committed','When this release version was frozen as an official release.'),
  ('wm','releases','release','eng','Release','The integer number of the release, starting with 1.  The current number in this field always designates a work-in-progress.  The number prior indicates the last public release.'),
  ('wm','releases','sver_2','eng','BS Version','Dummy column with a name indicating the version of these bootstrap tables (which can''t be managed by wyseman themselves).'),
  ('wm','role_members','level','eng','Level','What level this role has in the privilge'),
  ('wm','role_members','member','eng','Member','The username of a member of the named role'),
  ('wm','role_members','priv','eng','Privilege','The privilege this role relates to'),
  ('wm','role_members','role','eng','Role','The name of a role'),
  ('wm','table_data','cols','eng','Columns','Indicates how many columns are in the table'),
  ('wm','table_data','has_pkey','eng','Has Pkey','Indicates whether the table has a primary key defined in the database'),
  ('wm','table_data','obj','eng','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','table_data','system','eng','System','True if the table/view is built in to PostgreSQL'),
  ('wm','table_data','tab_kind','eng','Kind','Tells whether the relation is a table or a view'),
  ('wm','table_data','td_sch','eng','Schema Name','The schema the table is in'),
  ('wm','table_data','td_tab','eng','Table Name','The name of the table being described'),
  ('wm','table_lang','columns','eng','Columns','A JSON structure describing language information relevant to the columns in this table/view'),
  ('wm','table_lang','messages','eng','Messages','Human readable messages the computer may generate in connection with this table/view'),
  ('wm','table_lang','obj','eng','Object','The schema and table/view'),
  ('wm','table_meta','columns','eng','Columns','A JSON structure describing metadata information relevant to the columns in this table/view'),
  ('wm','table_meta','fkeys','eng','Foreign Keys','A JSON structure containing information about the foreign keys pointed to by this table'),
  ('wm','table_meta','obj','eng','Object','The schema and table/view'),
  ('wm','table_meta','pkey','eng','Primary Key','A JSON array describing the primary key fields for this table/view'),
  ('wm','table_pub','obj','eng','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','table_pub','sch','eng','Schema Name','The schema the table belongs to'),
  ('wm','table_pub','tab','eng','Table Name','The name of the table being described'),
  ('wm','table_style','inherit','eng','Inherit','The value for this style can propagate to derivative views'),
  ('wm','table_style','sw_name','eng','Name','The name of the style being described'),
  ('wm','table_style','sw_value','eng','Value','The value for this particular style'),
  ('wm','table_style','ts_sch','eng','Schema Name','The schema for the table this style pertains to'),
  ('wm','table_style','ts_tab','eng','Table Name','The name of the table this style pertains to'),
  ('wm','table_text','help','eng','Description','A longer description of what the table is used for'),
  ('wm','table_text','language','eng','Language','The language this description is in'),
  ('wm','table_text','title','eng','Title','A short title for the table'),
  ('wm','table_text','tt_sch','eng','Schema Name','The schema this table belongs to'),
  ('wm','table_text','tt_tab','eng','Table Name','The name of the table being described'),
  ('wm','value_text','help','eng','Description','A longer description of what it means when the column is set to this value'),
  ('wm','value_text','language','eng','Language','The language this description is in'),
  ('wm','value_text','title','eng','Title','A short title for the value'),
  ('wm','value_text','value','eng','Value','The name of the value being described'),
  ('wm','value_text','vt_col','eng','Column Name','The name of the column whose values are being described'),
  ('wm','value_text','vt_sch','eng','Schema Name','The schema of the table the column belongs to'),
  ('wm','value_text','vt_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','view_column_usage','column_name','eng','Column Name','The name of the column in the view'),
  ('wm','view_column_usage','table_catalog','eng','Table Database','The database the underlying table belongs to'),
  ('wm','view_column_usage','table_name','eng','Table Name','The name of the underlying table'),
  ('wm','view_column_usage','table_schema','eng','Table Schema','The schema the underlying table belongs to'),
  ('wm','view_column_usage','view_catalog','eng','View Database','The database the view belongs to'),
  ('wm','view_column_usage','view_name','eng','View Name','The name of the view being described'),
  ('wm','view_column_usage','view_schema','eng','View Schema','The schema the view belongs to'),
  ('wylib','data','access','eng','Access','Who is allowed to access this data, and how'),
  ('wylib','data','access','fin','Pääsy','Kuka saa käyttää näitä tietoja ja miten'),
  ('wylib','data','component','eng','Component','The part of the graphical, or other user interface that uses this data'),
  ('wylib','data','component','fin','Komponentti','GUI:n osa joka käyttää tämä data'),
  ('wylib','data','crt_by','eng','Created By','The user who entered this record'),
  ('wylib','data','crt_date','eng','Created','The date this record was created'),
  ('wylib','data','data','eng','JSON Data','A record in JSON (JavaScript Object Notation) in a format known and controlled by the view or other accessing module'),
  ('wylib','data','descr','eng','Description','A full description of what this configuration is for'),
  ('wylib','data','mod_by','eng','Modified By','The user who last modified this record'),
  ('wylib','data','mod_date','eng','Modified','The date this record was last modified'),
  ('wylib','data','name','eng','Name','A name explaining the version or configuration this data represents (i.e. Default, Searching, Alphabetical, Urgent, Active, etc.)'),
  ('wylib','data','owner','eng','Owner','The user entity who created and has full permission to the data in this record'),
  ('wylib','data','ruid','eng','Record ID','A unique ID number generated for each data record'),
  ('wylib','data','ruid','fin','Tunnistaa','Kullekin datatietueelle tuotettu yksilöllinen ID-numero'),
  ('wylib','data_v','own_name','eng','Owner Name','The name of the person who saved this configuration data');
insert into wm.value_text (vt_sch,vt_tab,vt_col,value,language,title,help) values
  ('base','addr','addr_type','bill','eng','Billing','Where invoices and other accounting information are sent'),
  ('base','addr','addr_type','mail','eng','Mailing','Where mail and correspondence is received'),
  ('base','addr','addr_type','phys','eng','Physical','Where the entity has people living or working'),
  ('base','addr','addr_type','ship','eng','Shipping','Where materials are picked up or delivered'),
  ('base','comm','comm_type','cell','eng','Cell','A way to contact the entity via cellular telephone'),
  ('base','comm','comm_type','email','eng','Email','A way to contact the entity via email'),
  ('base','comm','comm_type','fax','eng','FAX','A way to contact the entity via faxsimile'),
  ('base','comm','comm_type','other','eng','Other','Some other contact method for the entity'),
  ('base','comm','comm_type','pager','eng','Pager','A way to contact the entity via a mobile pager'),
  ('base','comm','comm_type','phone','eng','Phone','A way to contact the entity via telephone'),
  ('base','comm','comm_type','text','eng','Text Message','A way to contact the entity via email to text messaging'),
  ('base','comm','comm_type','web','eng','Web Address','A World Wide Web address URL for this entity'),
  ('base','ent','ent_type','g','eng','Group','The entity is a group of people, companies, and/or other groups'),
  ('base','ent','ent_type','o','eng','Organization','The entity is an organization (such as a company or partnership) which may employ or include members of individual people or other organizations'),
  ('base','ent','ent_type','p','eng','Person','The entity is an individual'),
  ('base','ent','ent_type','r','eng','Role','The entity is a role or position that may not correspond to a particular person or company'),
  ('base','ent','gender','','eng','N/A','Gender is not applicable (such as for organizations or groups)'),
  ('base','ent','gender','f','eng','Female','The person is female'),
  ('base','ent','gender','m','eng','Male','The person is male'),
  ('base','ent','marital','','eng','N/A','Marital status is not applicable (such as for organizations or groups)'),
  ('base','ent','marital','m','eng','Married','The person is in a current marriage'),
  ('base','ent','marital','s','eng','Single','The person has never married or is divorced or is the survivor of a deceased spouse'),
  ('base','file','file_type','other','eng','Other','Some other type of document'),
  ('base','file','file_type','photo','eng','Photograph','The document is a photogaph'),
  ('base','file','file_type','scan','eng','Scan','The document is a scan of a physical document'),
  ('base','file','file_type','spread','eng','Spreadsheet','The document is a spreadsheet'),
  ('base','file','file_type','write','eng','Written','The document is a written article, paper, etc'),
  ('base','parm','type','boolean','eng','Boolean','The parameter can contain only the values of true or false'),
  ('base','parm','type','date','eng','Date','The parameter can contain only date values'),
  ('base','parm','type','float','eng','Float','The parameter can contain only values of floating point type (integer portion, decimal, fractional portion)'),
  ('base','parm','type','int','eng','Integer','The parameter can contain only values of integer type (... -2, -1, 0, 1, 2 ...'),
  ('base','parm','type','text','eng','Text','The parameter can contain any text value'),
  ('mychips','chits','chit_type','lift','eng','Credit Lift','The transaction is part of a credit lift, so multiple chits should exist with the same ID number, which all net to zero in their effect to the relevant entity'),
  ('mychips','chits','chit_type','set','eng','User Setting','The chit evidences a party (stock or foil) having asserted a change of certain operating parameters of the tally'),
  ('mychips','chits','chit_type','tran','eng','Transaction','The credit is granted in exchange for present or future goods, services or other, possibly charitable, consideration.'),
  ('mychips','lifts','lift_type','in','eng','Inside','The lift is limited to within a single database'),
  ('mychips','lifts','lift_type','org','eng','Origin','The lift originated within the local database but is propagated to other sites'),
  ('mychips','lifts','lift_type','rel','eng','Relay','The lift originated in another site and was propagated to this site'),
  ('mychips','routes','status','draft','eng','Draft','The route has been requested but not yet checked or propagated upstream'),
  ('mychips','routes','status','good','eng','Good','The upstream peer server has answered that this route is possible'),
  ('mychips','routes','status','none','eng','None','The upstream peer server has answered that this route is not possible'),
  ('mychips','routes','status','pend','eng','Pending','A request has been made upstream to discover this route but no further status is yet known locally'),
  ('mychips','routes_v','sorter','0','eng','Good','The route is believed good and fresh'),
  ('mychips','routes_v','sorter','1','eng','Pending','Route queries have recently been generated but not resolved'),
  ('mychips','routes_v','sorter','2','eng','Expired Good','The route was good but expiration time has passed'),
  ('mychips','routes_v','sorter','3','eng','No Route','No route has been generated yet on this potential pathway'),
  ('mychips','routes_v','sorter','4','eng','Expired Pending','A request for the route was issued but no response has been received'),
  ('mychips','routes_v','sorter','5','eng','Other','The route is in some other state'),
  ('mychips','tallies','request','close','eng','Close','One party is requesting to discontinue further trading on this tally'),
  ('mychips','tallies','request','draft','eng','Draft','One party is suggesting terms for a tally'),
  ('mychips','tallies','request','open','eng','Open','One party is requesting to open the tally according to the specified terms'),
  ('mychips','tallies','request','void','eng','Void','One party has requested to negotiation before the tally has been opened'),
  ('mychips','tallies','status','close','eng','Close','No further trading can occur on this tally'),
  ('mychips','tallies','status','draft','eng','Draft','The tally have bee suggested by one party but not yet accepted by the other party'),
  ('mychips','tallies','status','open','eng','Open','The tally is affirmed by both parties and can be used for trading chits'),
  ('mychips','tallies','status','void','eng','Void','The tally has been abandoned before being affirmed by both parties'),
  ('mychips','tallies','tally_type','foil','eng','Foil','The entity this tally belongs to is typically the debtor on transactions'),
  ('mychips','tallies','tally_type','stock','eng','Stock','The entity this tally belongs to is typically the creditor on transactions'),
  ('mychips','users','user_stat','act','eng','Active','Good to conduct trades'),
  ('mychips','users','user_stat','act','fin','Aktiivinen','Hyvä käydä kauppaa'),
  ('mychips','users','user_stat','lck','eng','Lockdown','Account in emergency lockdown.  Do not conduct trades which result in a net loss of credit.'),
  ('mychips','users','user_stat','lck','fin','Lukittu','Tili hätätilanteessa. Älä harjoita kauppoja, jotka johtavat nettotappioon.'),
  ('mychips','users','user_stat','off','eng','Offline','Account completely off line.  No trades possible.'),
  ('mychips','users','user_stat','off','fin','Irrotettu','Tili kokonaan pois päältä. Kaupat eivät ole mahdollisia.'),
  ('wylib','data','access','priv','eng','Private','Only the owner of this data can read, write or delete it'),
  ('wylib','data','access','priv','fin','Yksityinen','Vain näiden tietojen omistaja voi lukea, kirjoittaa tai poistaa sen'),
  ('wylib','data','access','read','eng','Public Read','The owner can read and write, all others can read, or see it'),
  ('wylib','data','access','read','fin','Julkinen Lukea','Omistaja voi lukea ja kirjoittaa, kaikki muut voivat lukea tai nähdä sen'),
  ('wylib','data','access','write','eng','Public Write','Anyone can read, write, or delete this data'),
  ('wylib','data','access','write','fin','Julkinen Kirjoittaa','Jokainen voi lukea, kirjoittaa tai poistaa näitä tietoja');
insert into wm.message_text (mt_sch,mt_tab,code,language,title,help) values
  ('base','addr','CCO','eng','Country','The country must always be specified (and in standard form)'),
  ('base','addr','CPA','eng','Primary','There must be at least one address checked as primary'),
  ('base','addr','USP','eng','Duplicate','There should only be one record for each separate type and address'),
  ('base','comm','CPC','eng','Primary','There must be at least one communication point of each type checked as primary'),
  ('base','comm','USP','eng','Duplicate','There should only be one communication record for each separate type and number/address'),
  ('base','ent','CBD','eng','Born Date','A born date is required for inside people'),
  ('base','ent','CFN','eng','First Name','A first name is required for personal entities'),
  ('base','ent','CGN','eng','Gender','Gender must not be specified for non-personal entities'),
  ('base','ent','CMN','eng','Middle Name','A middle name is prohibited for non-personal entities'),
  ('base','ent','CMS','eng','Marital','Marital status must not be specified for non-personal entities'),
  ('base','ent','CPA','eng','Prime Addr','A primary address must be active'),
  ('base','ent','CPN','eng','Pref Name','A preferred name is prohibited for non-personal entities'),
  ('base','ent','CTI','eng','Title','A preferred title is prohibited for non-personal entities'),
  ('base','ent_link','NBP','eng','Illegal Entity Org','A personal entity can not be an organization (and have member entities)'),
  ('base','ent_link','PBC','eng','Illegal Entity Member','Only personal entities can belong to company entities'),
  ('base','ent_v','directory','eng','Directory','Report showing basic contact data for the selected entities'),
  ('base','file','USP','eng','Duplicate','There should only be one file for each separate type and checksum'),
  ('base','parm_v','launch.instruct','eng','Basic Instructions','
      <p>These settings control all kinds of different options on your system.
      <p>Each setting is interpreted within the context of the module it is intended for.
         System settings have descriptions initialized in the table.  Although you may be
         able to change these, you probably shouldn''t as they are installed there by the
         schema author to help you understand what the setting controls.
    '),
  ('base','parm_v','launch.title','eng','Settings','Site Operating Parameters'),
  ('base','priv','CLV','eng','Illegal Level','The privilege level must be null or a positive integer between 1 and 9'),
  ('base','priv_v','suspend','eng','Suspend User','Disable permissions for this user (not yet implemented)'),
  ('mychips','agents','AHP','eng','Unique Host/Port','Each agent key must be associated with a unique combination of host address and port'),
  ('mychips','agents','CHR','eng','Agent Host Required','A host or IP address for the agent must be specified'),
  ('mychips','agents','CPR','eng','Agent Port Required','A port number for the agent must be specified'),
  ('mychips','chits','BCT','eng','Bad Chit Type','Not a valid type for a tally chit'),
  ('mychips','chits','BLL','eng','Bad Lift Sequence','Only lift chits should include a lift sequence number'),
  ('mychips','chits','BST','eng','Bad Chit Status','Not a valid value the status field'),
  ('mychips','chits','CUN','eng','Bad Chit Units','Transactional chits must have a unit value.  Settings chits must not.'),
  ('mychips','chits','CUU','eng','Chit Not Unique','Chit UUID must be unique to each tally'),
  ('mychips','chits','GDS','eng','Signature Check','Chits in a good state must include a signature'),
  ('mychips','chits','IST','eng','Illegal State Change','The executed state transition is not allowed'),
  ('mychips','chits','LIT','eng','Link Invalid Tally','Attempted to link chit to invalid tally'),
  ('mychips','chits','MIS','eng','Bad Chit Signature','A chit marked to be good has no signature'),
  ('mychips','contracts','BVN','eng','Bad Version Number','Version number for contracts should start with 1 and move progressively larger'),
  ('mychips','contracts','ILR','eng','Illegal Rows','A query expecting a single record returned zero or multiple rows'),
  ('mychips','contracts','PBC','eng','Publish Constraints','When publishing a document, one must specify the digest hash, the source location, and the content sections'),
  ('mychips','contracts','UNC','eng','Unknown Command','The contract editor report received an unrecognized action command'),
  ('mychips','contracts_v','edit','eng','Edit Sections','Dedicated window for properly editing the contract sections'),
  ('mychips','contracts_v','IDK','eng','Invalid Key','The key values specified for the contract document are not valid'),
  ('mychips','contracts_v','launch.instruct','eng','Basic Instructions','
      <p>If your users use only contracts created and maintained by other parties, you 
         may not need to create any new data here.
      <p>You can create your own contracts and/or modify existing ones by opening an editing
         window and selecting Edit Sections from the Actions menu.
    '),
  ('mychips','contracts_v','launch.title','eng','Contracts','Manage Trading Agreements'),
  ('mychips','contracts_v','publish','eng','Publish','Commit this version, write the publication date, and disable further modifications'),
  ('mychips','contracts_v','TMK','eng','Bad Key Number','The contract report must be called with exactly one record ID'),
  ('mychips','lifts','CIF','eng','Chit Failure','An operation failed to create chits correctly for a lift'),
  ('mychips','lifts','IVR','eng','Invalid Request','At attempt was made to set a lift request to an unallowed value'),
  ('mychips','lifts','IVS','eng','Invalid Status','At attempt was made to set a lift status to an unallowed value'),
  ('mychips','lifts','IVT','eng','Invalid Type','At attempt was made to create a lift record with a disallowed type'),
  ('mychips','lifts','MDA','eng','Missing Agent','A destination CHIP address was given without specifying an agent address'),
  ('mychips','routes','BST','eng','Bad Route Status','Not a valid status for the route status'),
  ('mychips','routes','CRL','eng','Illegal Route Target','Routes should be only to users on other systems'),
  ('mychips','routes','LMG','eng','Illegal Margin','The margin must be specified between -1 and 1'),
  ('mychips','routes','LRW','eng','Illegal Reward','The reward must be specified between -1 and 1'),
  ('mychips','routes','UNI','eng','Not Unique Route','Routes should have a unique combination of source and destination'),
  ('mychips','tallies','BND','eng','Illegal Bound','Maximum lift boundary must be greater or equal to zero'),
  ('mychips','tallies','CLT','eng','Illegal Clutch','Lift clutch must be between -1 and 1'),
  ('mychips','tallies','IST','eng','Illegal State Change','The executed state transition is not allowed'),
  ('mychips','tallies','IVR','eng','Invalid Request','Tally request value is not valid'),
  ('mychips','tallies','IVS','eng','Invalid Status','Tally status value is not valid'),
  ('mychips','tallies','NSP','eng','Same Partner ID','Tally partner must be a separate entity'),
  ('mychips','tallies','PAI','eng','Partner Agent ID','An open tally must include a valid partner agent ID'),
  ('mychips','tallies','PCI','eng','Partner CHIP ID','An open tally must include a valid partner CHIP ID'),
  ('mychips','tallies','PCM','eng','Bad Partner Certificate','An open tally must contain a partner certificate'),
  ('mychips','tallies','PSM','eng','Bad Partner Signature','An open tally must contain a partner signature'),
  ('mychips','tallies','RWD','eng','Illegal Reward','Lift reward must be between -1 and 1'),
  ('mychips','tallies','TCM','eng','Bad Tally Contract','An open tally must contain a valid tally contract'),
  ('mychips','tallies','TGT','eng','Illegal Target','Lift target must be less than or equal to the maximum lift amount'),
  ('mychips','tallies','TNU','eng','Tally ID Not Unique','The chosen tally type and ID is not unique to the system'),
  ('mychips','tallies','UAI','eng','User Agent ID','An open tally must include a valid user agent ID'),
  ('mychips','tallies','UCI','eng','User CHIP ID','An open tally must include a valid user CHIP ID'),
  ('mychips','tallies','UCM','eng','Bad User Certificate','An open tally must contain a user certificate'),
  ('mychips','tallies','USM','eng','Bad User Signature','An open tally must contain a user signature'),
  ('mychips','tallies','VER','eng','Bad Tally Version','Tally version must be 1 or greater'),
  ('mychips','tallies_v_me','close','eng','Close Tally','Request that the current tally be closed once its balance reaches zero'),
  ('mychips','tallies_v_me','GTK','eng','Generating Tally','A database error occurred while generating a tally invitation ticket'),
  ('mychips','tallies_v_me','invite','eng','Invite to Tally','Create a new invitation to tally for a prospective partner'),
  ('mychips','tallies_v_me','invite.format','eng','Format','Determines which type of invitation is generated'),
  ('mychips','tallies_v_me','invite.format.json','eng','json','Return tally invitation as JSON object'),
  ('mychips','tallies_v_me','invite.format.link','eng','link','Return tally invitation as deep link Uniform Resource Locator'),
  ('mychips','tallies_v_me','invite.format.qr','eng','qr','Return tally invitation as a QR code'),
  ('mychips','tallies_v_me','invite.reuse','eng','Reusable','Create a tally template that can be reused over again with any number of trading partners'),
  ('mychips','tallies_v_me','launch.instruct','eng','Basic Instructions','
      <p>Tallies are used to document and track trading agreements between partners.
      <p>You can propose a new tally from the action menu in the Editing pane.
    '),
  ('mychips','tallies_v_me','launch.title','eng','Tallies','Peer Trading Relationships'),
  ('mychips','tallies_v_me','TIL','eng','Good Until','Invitation expires after this time'),
  ('mychips','tallies_v_me','TIN','eng','Tally Invitation','Follow link to consider tally'),
  ('mychips','tallies_v_me','TMK','eng','Bad Key Number','The tally invitation must be called for exactly one tally'),
  ('mychips','tallies_v_me','URF','eng','Unknown Format','Unknown format for a tally invitation'),
  ('mychips','tokens','X','eng','Y','Z'),
  ('mychips','users','ABC','fin','Koetus 1','Ensimmäinen testiviesti'),
  ('mychips','users','BCD','fin','Koetus 2','Toinen testiviesti'),
  ('mychips','users','BRM','eng','Birth Record Update','Birth record can only be written once by the user'),
  ('mychips','users','DEF','fin','Koetus 3','Kolmanen testiviesti'),
  ('mychips','users','UST','eng','Invalid Trading Status','A disallowed value for the user trading status was specified'),
  ('mychips','users_v','GTK','eng','Generating Ticket','A database error occurred while generating a user connection ticket'),
  ('mychips','users_v','launch.instruct','eng','Basic Instructions','
      <p>Users are people or companies who are hosted by this system.
      <p>A user account record may be created from scratch, or appended to an existing entity 
         record (and/or peer record).
         So if you are adding a new user, search first to see if they are already an existing peer
         or other entity, and then furnish the additional information to fill out the user fields.
    '),
  ('mychips','users_v','launch.title','eng','Users','User Account Management'),
  ('mychips','users_v','lock','eng','Lock Account','Put the specified account(s) into lockdown mode, so no further trading can occur'),
  ('mychips','users_v','summary','eng','Summary Report','Report about the current status of the selected user'),
  ('mychips','users_v','ticket','eng','User Ticket','Generate a temporary, one-time pass to allow a user to establish a secure connection with the server'),
  ('mychips','users_v','ticket.format','eng','Format','Determines which type of connection ticket is generated'),
  ('mychips','users_v','ticket.format.json','eng','json','Return connection ticket as JSON object'),
  ('mychips','users_v','ticket.format.link','eng','link','Return connection ticket as deep link Uniform Resource Locator'),
  ('mychips','users_v','ticket.format.qr','eng','qr','Return connection ticket as a QR code'),
  ('mychips','users_v','ticket.format.url','eng','url','Return connection ticket as an SPA Uniform Resource Locator'),
  ('mychips','users_v','TIL','eng','Good Until','Ticket expires after this time'),
  ('mychips','users_v','TIN','eng','Connection Ticket','Link to access your service provider'),
  ('mychips','users_v','TMK','eng','Bad Key Number','The connection ticket must be called for exactly one user'),
  ('mychips','users_v','trade','eng','Trading Report','Report showing trades in a given date range'),
  ('mychips','users_v','trade.end','eng','End Date','Include trades on and before this date'),
  ('mychips','users_v','trade.start','eng','Start Date','Include trades on and after this date'),
  ('mychips','users_v','unlock','eng','Unlock Account','Put the specified account(s) into functional mode, so normal trading can occur'),
  ('mychips','users_v','URF','eng','Unknown Format','Unknown format for a connection ticket'),
  ('mychips','users_v_me','launch.instruct','eng','Basic Instructions','
      <p>This view shows only the record pertaining to the connected user
    '),
  ('mychips','users_v_me','launch.title','eng','Current User','Current User Account Record'),
  ('mychips','users_v_tallies','centPull','eng','Centering','How hard nodes seek graph center'),
  ('mychips','users_v_tallies','floatSink','eng','Bouyancy','How hard assets rise and liabilities sink'),
  ('mychips','users_v_tallies','forPull','eng','Foreign Pull','How hard the link connector pulls on foreign nodes'),
  ('mychips','users_v_tallies','lenFor','eng','Foreign Links','Relative length of links with foreign nodes'),
  ('mychips','users_v_tallies','lenLoc','eng','Local Links','Relative length of links with other local user nodes'),
  ('mychips','users_v_tallies','locPull','eng','Local Pull','How hard the link connector pulls between local user nodes'),
  ('mychips','users_v_tallies','repel','eng','Node Repel','How hard nodes repel each other'),
  ('mychips','users_v_tallies','simDecay','eng','Alpha Decay','Controls how fast the simulation settles'),
  ('mychips','users_v_tallies','velDecay','eng','Velocity Decay','Simulates atmospheric friction'),
  ('mychips','users_v_tallies','vertAlign','eng','Vertical Align','How hard to push foriegn nodes to align with local user tally'),
  ('wm','lang','23505','eng','Key Violation','An operation would have resulted in multiple records having duplicated data, which is required to be unique'),
  ('wm','lang','badAction','eng','Invalid Action','The requested action was not recognized'),
  ('wm','lang','badDelete','eng','Invalid Delete','A delete command was too broadly specified'),
  ('wm','lang','badFieldName','eng','Field Error','A database field was not recognized'),
  ('wm','lang','badInsert','eng','Invalid Insert','There was no data found to insert'),
  ('wm','lang','badLeft','eng','Invalid Left Side','The left side of the comparison logic was not understood'),
  ('wm','lang','badLogic','eng','Invalid Logic','The logic structure was not understood'),
  ('wm','lang','badMessage','eng','Invalid Operation','The requested operation was not understood'),
  ('wm','lang','badOperator','eng','Invalid Operator','The specified logic operator is not understood'),
  ('wm','lang','badRight','eng','Invalid Right Side','The right side of the comparison logic was not understood'),
  ('wm','lang','badTuples','eng','No Record','No database record was returned where one was expected'),
  ('wm','lang','badUpdate','eng','Invalid Update','An update query produced nothing to update'),
  ('wm','lang','badWhere','eng','Invalid Where','The where-clause was not understood'),
  ('wm','lang','noResult','eng','No Result','The query did not produce the expected result'),
  ('wylib','data','23505','eng','Key Violation','An operation would have resulted in multiple records having duplicated data, which is required to be unique'),
  ('wylib','data','appDefault','eng','Default State','Reload the application to its default state (you will lose any unsaved configuration state, including connection keys)!'),
  ('wylib','data','appEditState','eng','Edit States','Preview a list of saved states for this application'),
  ('wylib','data','appLocalAsk','eng','Store Data in Browser','OK means the app can store sensitive information in your browser, including your private connection key.  This could be snooped by others who may have access to this computer!  If they get your key, they can connect to your data, logged in as you!  Cancel to not store application data in the browser.'),
  ('wylib','data','appLocalP1','eng','Your Pass Phrase','Enter a pass phrase which will be used to unlock your local storage, including connection keys.  If you leave this blank and press OK, your data will be stored unencrypted!'),
  ('wylib','data','appLocalP2','eng','Pass Phrase Check','Enter the pass phrase a second time'),
  ('wylib','data','appLocalPrompt','eng','Login Prompt','The app will show you this prompt each time you load the application in order to ask for your pass phrase'),
  ('wylib','data','app.mychips_admin','eng','MyCHIPs Administration','Manage administrative tasks for a MyCHIPs one or more servers'),
  ('wylib','data','appNoConnect','eng','Not Connected','The application is not connected to a backend server'),
  ('wylib','data','appPrefs','eng','Preferences','View/edit settings for the application or for a subcomponent'),
  ('wylib','data','appRestore','eng','Load State','Restore the application layout and operating state from a previously saved state'),
  ('wylib','data','appSave','eng','Save State','Re-save the layout and operating state of the application to the current named configuration, if there is one'),
  ('wylib','data','appSaveAs','eng','Save State As','Save the layout and operating state of the application, and all its subordinate windows, using a named configuration'),
  ('wylib','data','appServer','eng','Server','Toggle menu for connecting to various servers'),
  ('wylib','data','appServerURL','eng','Server URL','The domain and port of the server you are currently connected to'),
  ('wylib','data','appStateDescr','eng','State Description','A full description of the saved state and what you use it for'),
  ('wylib','data','appStatePrompt','eng','State ID Tag','The name or words you will use to identify this saved state when considering it for later recall'),
  ('wylib','data','appStateTag','eng','State Tag','The tag is a brief name you will refer to later when loading the saved state'),
  ('wylib','data','conConnect','eng','Connect','Attempt to connect to, or disconnect from the selected server'),
  ('wylib','data','conCryptErr','eng','Generating Key','There was an error in the browser attempting to generate a connection key'),
  ('wylib','data','conDelete','eng','Delete','Remove the selected server connections from the list'),
  ('wylib','data','conExpFile','eng','Key Filename','The file name to use for saving the selected private keys'),
  ('wylib','data','conExport','eng','Export Keys','Save the selected private connection keys out to a file.  Delete these files immediately after moving them to a private backup device.  Never leave them in the download area or on a live file system!'),
  ('wylib','data','conExpPass','eng','Key Passphrase','A secret passphrase to encrypt/decrypt private keys stored in an external format.  Leave blank (foolishly) for no encryption.'),
  ('wylib','data','conExpPass2','eng','Re-enter Passphrase','Enter passphrase again'),
  ('wylib','data','conImport','eng','Import Keys','Drag/drop key files here, or click to import a connection key, or one-time connection ticket'),
  ('wylib','data','conmenu','eng','Connection Menu','Various helper functions to control how you connect to server sites, and manage your connection keys'),
  ('wylib','data','conNoCrypto','eng','No Crypto Library','Cryptographic functions not found in browser API.  Make sure you are connected by https, or use a more modern browser.'),
  ('wylib','data','conRetry','eng','Retrying in','Will attempt to automatically reconnect to the server'),
  ('wylib','data','conTitle','eng','Connection Keys','A list of credentials, servers and ports where you normally connect.  Get a ticket from the site administrator where you want to connect.'),
  ('wylib','data','conUsername','eng','Username','Input the name you will use to connect to the backend database.  If you don''t know.  Ask the person who issued your connection ticket.'),
  ('wylib','data','dbe','eng','Edit Records','Insert, change and delete records from the database view'),
  ('wylib','data','dbeActions','eng','Actions','Perform various commands pertaining to this particular view and record'),
  ('wylib','data','dbeActions','fin','Tehköjä','Tehdä muutamia asioita tämän mukaisesti'),
  ('wylib','data','dbeClear','eng','Clear','Empty the editing fields, discontinue editing any database record that may have been loaded'),
  ('wylib','data','dbeColMenu','eng','Column','Operations you can perform on this column of the preview'),
  ('wylib','data','dbeDelete','eng','Delete','Delete this database record (can not be un-done)'),
  ('wylib','data','dbeInsert','eng','Add New','Insert a new record into the database table'),
  ('wylib','data','dbeLoadPrompt','eng','Primary Key Value(s)','Input the primary key field values for the record you want to load'),
  ('wylib','data','dbeLoadRec','eng','Load Record','Load a specific record from the database by its primary key'),
  ('wylib','data','dbeMenu','eng','Editing','A menu of functions for editing a database record'),
  ('wylib','data','dbeNoPkey','eng','No Primary key','The report update could not determine the primary key fields for the record.  Any changes may be lost.'),
  ('wylib','data','dbeOption','eng','Optional Fields','Show additional information about this record'),
  ('wylib','data','dbePopupErr','eng','Popup Failed','Error trying to open a pop-up window.  Is the browser blocking pop-ups?'),
  ('wylib','data','dbePreview','eng','Preview Document','Preview this record as a document'),
  ('wylib','data','dbePrimary','eng','Primary Key','The value that uniquely identifies the current record among all the rows in the database table'),
  ('wylib','data','dbeRecordID','eng','Record ID','Load a record by specifying its primary key values directly'),
  ('wylib','data','dbeSubords','eng','Preview','Toggle the viewing of views and records which relate to the currently loaded record'),
  ('wylib','data','dbeUpdate','eng','Update','Modify changed fields in the existing database record'),
  ('wylib','data','dbp','eng','Preview','A window for showing the records of a database table in a grid like a spreadsheet'),
  ('wylib','data','dbpAutoLoad','eng','Auto Execute','Automatically execute the top row any time the preview is reloaded'),
  ('wylib','data','dbpClear','eng','Clear Preview','Remove contents of the preview window, with no records loaded'),
  ('wylib','data','dbpColAuto','eng','Auto Size','Adjust the width of this column to be optimal for its contents'),
  ('wylib','data','dbpColHide','eng','Hide Column','Remove this column from the display'),
  ('wylib','data','dbpColumn','eng','Column Menu','Menu of commands to control this column display'),
  ('wylib','data','dbpDefault','eng','Default Columns','Set all column display and order to the database default'),
  ('wylib','data','dbpExport','eng','Export Records','Save the selected records to a local file'),
  ('wylib','data','dbpExportAsk','eng','Export File','Supply a filename to use when exporting'),
  ('wylib','data','dbpExportFmt','eng','Pretty','Export the file with indentation to make it more easily readable by people'),
  ('wylib','data','dbpFilter','eng','Filter','Load records according to filter criteria'),
  ('wylib','data','dbpFilter','fin','Suodattaa','Lataa tietueet suodatuskriteerien mukaisesti'),
  ('wylib','data','dbpFooter','fin','Yhteenveto','Ota ruutuun käyttöön sarakeyhteenveto'),
  ('wylib','data','dbpLoad','eng','Load Default','Load the records normally displayed in this view'),
  ('wylib','data','dbpLoad','fin','Ladata Oletus','Aseta tässä näkymässä näkyvät kirjaukset oletuksena'),
  ('wylib','data','dbpLoadAll','eng','Load All','Load all records from this table'),
  ('wylib','data','dbpLoadAll','fin','Loadata Kaikki','Lataa kaikki taulukon tiedot'),
  ('wylib','data','dbpLoaded','eng','Loaded Records','How many records are currently loaded in the preview'),
  ('wylib','data','dbpMenu','eng','Preview Menu','A menu of functions for operating on the preview list below'),
  ('wylib','data','dbpMenu','fin','Esikatselu','Toimintojen valikko, joka toimii alla olevassa esikatselussa'),
  ('wylib','data','dbpNext','eng','Next Record','Move the selection down one line and execute (normally edit) that new line'),
  ('wylib','data','dbpNoPkey','eng','No Primary key','The system could not determine the primary key fields for this table or view'),
  ('wylib','data','dbpPrev','eng','Prior Record','Move the selection up one line and execute (normally edit) that new line'),
  ('wylib','data','dbpReload','eng','Reload','Reload the records specified in the previous load'),
  ('wylib','data','dbpReload','fin','Ladata','Päivitä edellisessä kuormassa määritetyt tietueet'),
  ('wylib','data','dbpShowSum','eng','Show Summaries','Show a summary row at the bottom of the preview.  Use context menu in column to determine which summary function for each column.'),
  ('wylib','data','dbpVisCheck','eng','Visible','Check the box to make this column visible'),
  ('wylib','data','dbpVisCheck','fin','Ilmoita näkyvyydestä','Kirjoita tämä ruutu näkyviin, jotta tämä sarake voidaan näyttää'),
  ('wylib','data','dbpVisible','eng','Visible','Specify which columns are visible in the preview'),
  ('wylib','data','dbpVisible','fin','Näkyvyys','Sarakkeiden valikko, josta voit päättää, mitkä näkyvät esikatselussa'),
  ('wylib','data','dbs','eng','Filter Search','Load records according to filter criteria'),
  ('wylib','data','dbsClear','eng','Clear Query','Clear all logic terms'),
  ('wylib','data','dbsDefault','eng','Default Load','Load the query indicating how records are normally loaded (by default) from this table'),
  ('wylib','data','dbsDiff','eng','Diff','The left side is different from the right, in a comparison where two nulls (unassigned values) can be thought of as being the same'),
  ('wylib','data','dbsEqual','eng','=','The left and right side of the comparison are equal'),
  ('wylib','data','dbsIn','eng','In','The left value exists in a comma separated list you specify, or an array in another database field'),
  ('wylib','data','dbsLess','eng','<','The left value is less than the value on the right'),
  ('wylib','data','dbsLessEq','eng','<=','The left value is less than or equal to the value on the right'),
  ('wylib','data','dbsMore','eng','>','The left value is greater than the value on the right'),
  ('wylib','data','dbsMoreEq','eng','>=','The left value is greater than or equal to the value on the right'),
  ('wylib','data','dbsNop','eng','<Nop>','This operation causes the whole comparison clause to be ignored'),
  ('wylib','data','dbsNull','eng','Null','The value on the left is a null, or not assigned'),
  ('wylib','data','dbsRecall','eng','Recall Query','Recall a named query which has been previously saved'),
  ('wylib','data','dbsRexExp','eng','~','The left value matches a regular expression given by the value on the right'),
  ('wylib','data','dbsSave','eng','Save Query','Save the current query for future use'),
  ('wylib','data','dbsSearch','eng','Query Search','Run the configured selection query, returning matching records'),
  ('wylib','data','dbsTrue','eng','True','The left value is a boolean with a true value'),
  ('wylib','data','diaApply','eng','Perform','Perform the action associated with this dialog, but do not close it'),
  ('wylib','data','diaCancel','eng','Cancel','Abandon the operation associated with the dialog'),
  ('wylib','data','diaConfirm','eng','Confirm','The user is asked to confirm before proceeding, or cancel to abandon the operation'),
  ('wylib','data','diaDialog','eng','Dialog','Query user for specified input values or parameters'),
  ('wylib','data','diaError','eng','Error','Something went wrong'),
  ('wylib','data','diaNotice','eng','Notice','The message is a warning or advice for the user'),
  ('wylib','data','diaOK','eng','OK','Acknowledge you have seen the posted message'),
  ('wylib','data','diaQuery','eng','Input','The user is asked for certain input data, and a confirmation before proceeding'),
  ('wylib','data','diaReport','eng','Report','Report window'),
  ('wylib','data','diaYes','eng','OK','Proceed with the proposed operation and close the dialog'),
  ('wylib','data','IAT','eng','Invalid Access Type','Access type must be: priv, read, or write'),
  ('wylib','data','IAT','fin','Virheellinen käyttötyyppi','Käytön tyypin on oltava: priv, lukea tai kirjoittaa'),
  ('wylib','data','lchAdd','eng','Launch Preview','Use this button to open as many new database previews as you like'),
  ('wylib','data','lchImport','eng','Importer','Drag/drop files here, or click and browse, to import data from a JSON formatted file'),
  ('wylib','data','litCompare','eng','Comparison','Specify an operator for the comparison'),
  ('wylib','data','litLeft','eng','Left Side','Specify a field from the database to compare'),
  ('wylib','data','litManual','eng','Manual Entry','Enter a value manually to the right'),
  ('wylib','data','litNot','eng','Not','If asserted, the sense of the comparison will be negated, or made opposite'),
  ('wylib','data','litRemove','eng','Remove Item','Remove this item from the comparison list'),
  ('wylib','data','litRight','eng','Right Side','Specify a field from the database, or manual entry to compare'),
  ('wylib','data','litRightVal','eng','Right Value','Specify an explicit right-hand value for the comparision'),
  ('wylib','data','litToSub','eng','To Subgroup','Move this item to a deeper sub-group'),
  ('wylib','data','lstAddCond','eng','Add Condition','Add another condition for comparison'),
  ('wylib','data','lstAndOr','eng','And/Or','Specify whether all conditions must be true (and), or just one or more (or)'),
  ('wylib','data','lstRemove','eng','Remove Grouping','Remove this group of conditions'),
  ('wylib','data','mdewMore','eng','More Fields','Click to see more data fields pertaining to this record'),
  ('wylib','data','sdc','eng','Structured Document','An editor for documents structured in an outline format'),
  ('wylib','data','sdcAdd','eng','Add Subsection','Create a new paragraph or section nested below this one'),
  ('wylib','data','sdcBold','eng','Bold','Mark the highlighted text as bold'),
  ('wylib','data','sdcClear','eng','Clear','Delete the contents of the document on the screen.  Does not affect the database.'),
  ('wylib','data','sdcClearAsk','eng','Clear WorkSpace','Are you sure you want to clear the document data?'),
  ('wylib','data','sdcCross','eng','Cross Reference','Wrap the highlighted text with a cross reference.  The text should be a tag name for another section.  That section number will be substituted for the tag name.'),
  ('wylib','data','sdcDelete','eng','Delete Section','Delete this section of the document, and all its subsections'),
  ('wylib','data','sdcEdit','eng','Direct Editing','This section or paragraph is in direct editing mode.  Double click on the background to return to preview mode.'),
  ('wylib','data','sdcEditAll','eng','Edit All','Put all paragraphs or sections into direct editing mode.  This can be done one at a time by double clicking on the paragraph.'),
  ('wylib','data','sdcExport','eng','Export To File','Save the document to an external file'),
  ('wylib','data','sdcExportAsk','eng','Export File','Input a filename to use when exporting'),
  ('wylib','data','sdcExportFmt','eng','Pretty','Export the file with indentation to make it more easily readable by people'),
  ('wylib','data','sdcImport','eng','File Import','Load the workspace from an externally saved file'),
  ('wylib','data','sdcImportAsk','eng','Import From File','Select a file to Import, or drag it onto the import button'),
  ('wylib','data','sdcItalic','eng','Italic','Mark the highlighted text as italic'),
  ('wylib','data','sdcMenu','eng','Document Menu','A menu of functions for working with structured documents'),
  ('wylib','data','sdcPrevAll','eng','Preview All','Take all paragraphs or sections out of direct editing mode, and into preview mode'),
  ('wylib','data','sdcPreview','eng','Preview Mode','This section or paragraph is in preview mode.  Double click on the background to go to editing mode.'),
  ('wylib','data','sdcReference','eng','Reference','The following external document is incorporated by reference, becoming a part of this document'),
  ('wylib','data','sdcSection','eng','Section','Click to edit text.  Double click at edge for direct editing mode.  Drag at edge to move.'),
  ('wylib','data','sdcSource','eng','Source','The URL of another document which will be incorporated into this document by reference'),
  ('wylib','data','sdcSpell','eng','Spell Checking','Enable/disable spell checking in on the screen'),
  ('wylib','data','sdcTag','eng','Tag','An identifying word that can be used to cross-reference to this section or paragraph'),
  ('wylib','data','sdcText','eng','Paragraph Text','Insert/Edit the raw paragraph text directly here, including entering limited HTML tags, if desired'),
  ('wylib','data','sdcTitle','eng','Title','An optional title for this section or paragraph'),
  ('wylib','data','sdcTogSource','eng','Add Reference','Use this section to refer to some external document by its URL'),
  ('wylib','data','sdcUnder','eng','Underline','Underline highlighted text'),
  ('wylib','data','sdcUndo','eng','Undo','Reverse the effect of a paragraph deletion or move'),
  ('wylib','data','sdcUpdate','eng','Update','Save changes to this document back to the database'),
  ('wylib','data','subWindow','eng','Subordinate View','Open a preview of records in another table that relate to the currently loaded record from this view'),
  ('wylib','data','svgCurve','eng','Connector Curve','How far to extend graph edge curve control points'),
  ('wylib','data','svgDefaults','eng','Defaults','Restore adjustments to default settings'),
  ('wylib','data','svgExtent','eng','Auto Zoom','Zoom chart to show all nodes'),
  ('wylib','data','svgRefresh','eng','Refresh','Refresh chart from its source data'),
  ('wylib','data','svgReset','eng','Reset','Clear chart and then refresh it from source data'),
  ('wylib','data','winClose','eng','Close Window','Close this window'),
  ('wylib','data','winDefault','eng','Default State','Erase locally stored configuration data for this window'),
  ('wylib','data','winGeom','eng','Default Geometry','Let this window size itself according to its default setting'),
  ('wylib','data','winMenu','eng','Window Functions','A menu of functions for the display and operation of this window'),
  ('wylib','data','winMinimize','eng','Minimize','Shrink window down to an icon by which it can be re-opened'),
  ('wylib','data','winModified','eng','Close Modified Pane','Changes may be lost if you close the window'),
  ('wylib','data','winPinned','eng','Window Pinned','Keep this window open until it is explicitly closed'),
  ('wylib','data','winPopUp','eng','Printable Popup','Make a copy, if possible, of this window in a separate popup window so it can be printed, separate from the rest of the page'),
  ('wylib','data','winPrint','eng','Print Document','Find the nearest independent document (iframe) within this component, and print it'),
  ('wylib','data','winRestore','eng','Load State','Restore the the window''s layout and operating state from a previously saved state'),
  ('wylib','data','winSave','eng','Save State','Re-save the layout and operating state of this window to the current named configuration, if there is one'),
  ('wylib','data','winSaveAs','eng','Save State As','Save the layout and operating state of this window, and all its subordinate windows, to a named configuration'),
  ('wylib','data','winToBottom','eng','Move To Bottom','Place this window behind others of its peers'),
  ('wylib','data','winToTop','eng','Move To Top','Make this window show above others of its peers (can also double click on a window header)'),
  ('wylib','data','winUnCode','eng','Unknown Error Code','An error message was returned with an unrecognized code or status'),
  ('wylib','data','winUnknown','eng','Unknown Message','An error or query was generated that could not be understood by the program'),
  ('wylib','data','X','eng','',''),
  ('wylib','data','X.dbpColSel','eng','Visible Columns','Show or hide individual columns'),
  ('wylib','data','X.dbpFooter','eng','Footer','Check the box to turn on column summaries, at the bottom');
insert into wm.table_style (ts_sch,ts_tab,sw_name,sw_value,inherit) values
  ('base','addr','focus','"addr_spec"','t'),
  ('base','addr_v','display','["addr_type", "addr_spec", "state", "city", "pcode", "country", "addr_cmt", "addr_seq"]','t'),
  ('base','comm','focus','"file_type"','t'),
  ('base','comm_v','display','["comm_type", "comm_spec", "comm_cmt", "comm_seq"]','t'),
  ('base','ent','display','["id", "ent_type", "ent_name", "fir_name", "born_date"]','t'),
  ('base','ent','focus','"ent_name"','t'),
  ('base','ent_link','focus','"org_id"','t'),
  ('base','ent_v','actions','[{"name": "directory"}]','f'),
  ('base','ent_v','subviews','["base.addr_v", "base.comm_v", "base.priv_v"]','t'),
  ('base','ent_v_pub','focus','"ent_name"','t'),
  ('base','file_v','display','["file_type", "file_cks", "file_cmt", "file_seq"]','t'),
  ('base','parm_v','display','["module", "parm", "type", "value", "cmt"]','t'),
  ('base','parm_v','focus','"module"','t'),
  ('base','priv','focus','"priv"','t'),
  ('base','priv_v','actions','[{"name": "suspend"}]','f'),
  ('mychips','chits_v','display','["chit_ent", "chit_seq", "chit_idx", "chit_type", "units", "value"]','t'),
  ('mychips','chits_v_me','display','["chit_ent", "chit_seq", "chit_idx", "chit_type", "units", "value"]','t'),
  ('mychips','contracts','display','["domain", "name", "version", "language", "released", "source", "title"]','t'),
  ('mychips','contracts','focus','"domain"','t'),
  ('mychips','contracts_v','actions','[{"name": "edit", "slave": true, "render": "strdoc"}, {"ask": true, "name": "publish"}]','f'),
  ('mychips','contracts_v','export','"contract"','t'),
  ('mychips','contracts_v','launch','{"import": "json.import", "initial": 1}','t'),
  ('mychips','routes','display','["route_ent", "dest_ent", "dest_chid", "dest_host", "status"]','t'),
  ('mychips','routes_v','display','["route_ent", "route_addr", "dest_ent", "dest_addr", "status"]','t'),
  ('mychips','routes_v_lifts','display','["route_ent", "route_addr", "dest_ent", "dest_addr", "status"]','t'),
  ('mychips','tallies','display','["tally_ent", "tally_seq", "tally_type", "status", "part_ent", "tally_date", "tally_uuid", "dr_limit", "cr_limit", "reward", "target"]','t'),
  ('mychips','tallies_v','display','["tally_ent", "tally_seq", "tally_type", "status", "part_ent", "part_name", "reward", "dr_limit", "cr_limit", "target"]','t'),
  ('mychips','tallies_v_liftss','display','["bang", "length", "min", "max", "fora", "forz", "path"]','t'),
  ('mychips','tallies_v_me','actions','[{"ask": "1", "name": "close"}, {"name": "invite", "render": "html", "options": [{"tag": "reuse", "input": "chk", "onvalue": "t", "offvalue": "f"}, {"tag": "format", "input": "pdm", "values": ["qr", "link", "json"]}]}]','f'),
  ('mychips','tallies_v_me','display','["tally_ent", "tally_seq", "tally_type", "part_ent", "part_name", "dr_limit", "cr_limit", "total"]','t'),
  ('mychips','tallies_v_me','launch','{"import": "json.import", "initial": 1}','t'),
  ('mychips','tallies_v_me','subviews','["mychips.chits_v_me"]','t'),
  ('mychips','tallies_v_me','where','{"and": true, "items": [{"left": "status", "oper": "=", "entry": "open"}]}','t'),
  ('mychips','tallies_v_paths','display','["bang", "length", "min", "max", "circuit", "path"]','t'),
  ('mychips','users','focus','"ent_name"','t'),
  ('mychips','users_v','actions','[{"name": "ticket", "render": "html", "single": "1", "options": [{"tag": "format", "input": "pdm", "values": ["qr", "link", "url", "json"]}]}, {"ask": "1", "name": "lock"}, {"ask": "1", "name": "unlock"}, {"name": "summary", "render": "html"}, {"name": "trade", "render": "html", "options": [{"tag": "start", "hint": "date", "size": "11", "type": "date", "input": "ent", "special": "cal", "subframe": "1 1", "template": "date"}, {"tag": "end", "hint": "date", "size": "11", "type": "date", "input": "ent", "special": "cal", "subframe": "1 2", "template": "date"}]}]','f'),
  ('mychips','users_v','display','["id", "std_name", "ent_type", "user_stat", "user_sock", "born_date", "!fir_name", "!ent_name"]','t'),
  ('mychips','users_v','export','"user"','t'),
  ('mychips','users_v','launch','{"import": "json.import", "initial": 1}','t'),
  ('mychips','users_v','subviews','["base.addr_v", "base.comm_v"]','t'),
  ('mychips','users_v','where','{"and": true, "items": [{"not": true, "left": "user_ent", "oper": "isnull"}, {"not": true, "left": "ent_inact", "oper": "true"}, {"left": "ent_type", "oper": "=", "entry": "p"}]}','t'),
  ('mychips','users_v_flat','display','["id", "user_cid", "std_name", "bill_addr", "bill_city", "bill_state"]','t'),
  ('mychips','users_v_me','actions','[{"name": "graph", "render": "html", "single": "1"}]','f'),
  ('wm','column_pub','focus','"code"','t'),
  ('wm','column_text','focus','"code"','t'),
  ('wm','message_text','focus','"code"','t'),
  ('wm','objects','focus','"obj_nam"','t'),
  ('wm','table_text','focus','"code"','t'),
  ('wm','value_text','focus','"code"','t'),
  ('wylib','data','display','["ruid", "component", "name", "descr", "owner", "access"]','t'),
  ('wylib','data_v','display','["ruid", "component", "name", "descr", "own_name", "access"]','t');
insert into wm.column_style (cs_sch,cs_tab,cs_col,sw_name,sw_value) values
  ('base','addr','addr_cmt','input','ent'),
  ('base','addr','addr_cmt','size','50'),
  ('base','addr','addr_cmt','special','edw'),
  ('base','addr','addr_cmt','subframe','1 5 4'),
  ('base','addr','addr_ent','input','ent'),
  ('base','addr','addr_ent','justify','r'),
  ('base','addr','addr_ent','optional','1'),
  ('base','addr','addr_ent','size','5'),
  ('base','addr','addr_ent','state','readonly'),
  ('base','addr','addr_ent','subframe','1 6'),
  ('base','addr','addr_inact','initial','false'),
  ('base','addr','addr_inact','input','chk'),
  ('base','addr','addr_inact','size','2'),
  ('base','addr','addr_inact','subframe','2 3'),
  ('base','addr','addr_seq','hide','1'),
  ('base','addr','addr_seq','input','ent'),
  ('base','addr','addr_seq','justify','r'),
  ('base','addr','addr_seq','size','4'),
  ('base','addr','addr_seq','state','readonly'),
  ('base','addr','addr_seq','subframe','10 1'),
  ('base','addr','addr_seq','write','0'),
  ('base','addr','addr_spec','input','ent'),
  ('base','addr','addr_spec','size','30'),
  ('base','addr','addr_spec','special','edw'),
  ('base','addr','addr_spec','subframe','1 2 2'),
  ('base','addr','addr_type','initial','mail'),
  ('base','addr','addr_type','input','pdm'),
  ('base','addr','addr_type','size','6'),
  ('base','addr','addr_type','subframe','1 3'),
  ('base','addr','city','input','ent'),
  ('base','addr','city','size','24'),
  ('base','addr','city','subframe','2 1'),
  ('base','addr','country','data','country'),
  ('base','addr','country','input','ent'),
  ('base','addr','country','size','4'),
  ('base','addr','country','special','scm'),
  ('base','addr','country','subframe','3 2'),
  ('base','addr','crt_by','input','ent'),
  ('base','addr','crt_by','optional','1'),
  ('base','addr','crt_by','size','10'),
  ('base','addr','crt_by','state','readonly'),
  ('base','addr','crt_by','subframe','1 98'),
  ('base','addr','crt_by','write','0'),
  ('base','addr','crt_date','input','inf'),
  ('base','addr','crt_date','optional','1'),
  ('base','addr','crt_date','size','18'),
  ('base','addr','crt_date','state','readonly'),
  ('base','addr','crt_date','subframe','2 98'),
  ('base','addr','crt_date','write','0'),
  ('base','addr','dirty','hide','1'),
  ('base','addr','dirty','input','chk'),
  ('base','addr','dirty','size','2'),
  ('base','addr','dirty','subframe',''),
  ('base','addr','dirty','write','0'),
  ('base','addr','mod_by','input','ent'),
  ('base','addr','mod_by','optional','1'),
  ('base','addr','mod_by','size','10'),
  ('base','addr','mod_by','state','readonly'),
  ('base','addr','mod_by','subframe','1 99'),
  ('base','addr','mod_by','write','0'),
  ('base','addr','mod_date','input','inf'),
  ('base','addr','mod_date','optional','1'),
  ('base','addr','mod_date','size','18'),
  ('base','addr','mod_date','state','readonly'),
  ('base','addr','mod_date','subframe','2 99'),
  ('base','addr','mod_date','write','0'),
  ('base','addr','pcode','focus','true'),
  ('base','addr','pcode','input','ent'),
  ('base','addr','pcode','size','10'),
  ('base','addr','pcode','special','zip'),
  ('base','addr','pcode','subframe','1 1'),
  ('base','addr','physical','initial','true'),
  ('base','addr','physical','input','chk'),
  ('base','addr','physical','size','2'),
  ('base','addr','physical','subframe','3 3'),
  ('base','addr','state','data','state'),
  ('base','addr','state','input','ent'),
  ('base','addr','state','size','4'),
  ('base','addr','state','special','scm'),
  ('base','addr','state','subframe','3 1'),
  ('base','addr_v','addr_cmt','display','7'),
  ('base','addr_v','addr_prim','initial','false'),
  ('base','addr_v','addr_prim','input','chk'),
  ('base','addr_v','addr_prim','size','2'),
  ('base','addr_v','addr_prim','state','readonly'),
  ('base','addr_v','addr_prim','subframe','3 3'),
  ('base','addr_v','addr_prim','write','0'),
  ('base','addr_v','addr_seq','display','8'),
  ('base','addr_v','addr_seq','sort','2'),
  ('base','addr_v','addr_spec','display','2'),
  ('base','addr_v','addr_type','display','1'),
  ('base','addr_v','addr_type','sort','1'),
  ('base','addr_v','city','display','4'),
  ('base','addr_v','country','display','6'),
  ('base','addr_v','pcode','display','5'),
  ('base','addr_v','state','display','3'),
  ('base','addr_v','std_name','depend','addr_ent'),
  ('base','addr_v','std_name','in','addr_ent'),
  ('base','addr_v','std_name','input','ent'),
  ('base','addr_v','std_name','optional','1'),
  ('base','addr_v','std_name','size','14'),
  ('base','addr_v','std_name','subframe','2 6 2'),
  ('base','addr_v','std_name','title',':'),
  ('base','comm','crt_by','input','ent'),
  ('base','comm','crt_by','optional','1'),
  ('base','comm','crt_by','size','10'),
  ('base','comm','crt_by','state','readonly'),
  ('base','comm','crt_by','subframe','1 98'),
  ('base','comm','crt_by','write','0'),
  ('base','comm','crt_date','input','inf'),
  ('base','comm','crt_date','optional','1'),
  ('base','comm','crt_date','size','18'),
  ('base','comm','crt_date','state','readonly'),
  ('base','comm','crt_date','subframe','2 98'),
  ('base','comm','crt_date','write','0'),
  ('base','comm','file_cmt','input','ent'),
  ('base','comm','file_cmt','size','50'),
  ('base','comm','file_cmt','special','edw'),
  ('base','comm','file_cmt','subframe','1 3 3'),
  ('base','comm','file_ent','input','ent'),
  ('base','comm','file_ent','justify','r'),
  ('base','comm','file_ent','optional','1'),
  ('base','comm','file_ent','size','5'),
  ('base','comm','file_ent','state','readonly'),
  ('base','comm','file_ent','subframe','1 5'),
  ('base','comm','file_fmt','input','ent'),
  ('base','comm','file_fmt','size','10'),
  ('base','comm','file_fmt','subframe','2 2'),
  ('base','comm','file_seq','hide','1'),
  ('base','comm','file_seq','input','ent'),
  ('base','comm','file_seq','justify','r'),
  ('base','comm','file_seq','size','5'),
  ('base','comm','file_seq','state','readonly'),
  ('base','comm','file_seq','subframe','0 1'),
  ('base','comm','file_seq','write','0'),
  ('base','comm','file_type','focus','true'),
  ('base','comm','file_type','initial','phone'),
  ('base','comm','file_type','input','pdm'),
  ('base','comm','file_type','size','5'),
  ('base','comm','file_type','subframe','1 2'),
  ('base','comm','mod_by','input','ent'),
  ('base','comm','mod_by','optional','1'),
  ('base','comm','mod_by','size','10'),
  ('base','comm','mod_by','state','readonly'),
  ('base','comm','mod_by','subframe','1 99'),
  ('base','comm','mod_by','write','0'),
  ('base','comm','mod_date','input','inf'),
  ('base','comm','mod_date','optional','1'),
  ('base','comm','mod_date','size','18'),
  ('base','comm','mod_date','state','readonly'),
  ('base','comm','mod_date','subframe','2 99'),
  ('base','comm','mod_date','write','0'),
  ('base','comm_v','comm_cmt','display','3'),
  ('base','comm_v','comm_prim','initial','false'),
  ('base','comm_v','comm_prim','input','chk'),
  ('base','comm_v','comm_prim','offvalue','f'),
  ('base','comm_v','comm_prim','onvalue','t'),
  ('base','comm_v','comm_prim','size','2'),
  ('base','comm_v','comm_prim','state','readonly'),
  ('base','comm_v','comm_prim','subframe','3 2'),
  ('base','comm_v','comm_prim','write','0'),
  ('base','comm_v','comm_seq','display','4'),
  ('base','comm_v','comm_seq','sort','2'),
  ('base','comm_v','comm_spec','display','2'),
  ('base','comm_v','comm_type','display','1'),
  ('base','comm_v','comm_type','sort','1'),
  ('base','comm_v','std_name','depend','comm_ent'),
  ('base','comm_v','std_name','in','comm_ent'),
  ('base','comm_v','std_name','input','ent'),
  ('base','comm_v','std_name','optional','1'),
  ('base','comm_v','std_name','size','14'),
  ('base','comm_v','std_name','subframe','2 5 2'),
  ('base','comm_v','std_name','title',':'),
  ('base','ent','bank','hint','####:#### or ####:####:s'),
  ('base','ent','bank','input','ent'),
  ('base','ent','bank','size','14'),
  ('base','ent','bank','subframe','1 5'),
  ('base','ent','bank','template',E'^(|\\d+:\\d+|\\d+:\\d+:\\d+)$'),
  ('base','ent','born_date','display','5'),
  ('base','ent','born_date','hint','date'),
  ('base','ent','born_date','input','ent'),
  ('base','ent','born_date','size','11'),
  ('base','ent','born_date','special','cal'),
  ('base','ent','born_date','subframe','1 4'),
  ('base','ent','born_date','template','date'),
  ('base','ent','conn_key','input','ent'),
  ('base','ent','conn_key','size','8'),
  ('base','ent','conn_key','subframe','3 5'),
  ('base','ent','conn_key','write','0'),
  ('base','ent','country','data','country'),
  ('base','ent','country','input','ent'),
  ('base','ent','country','size','4'),
  ('base','ent','country','special','scm'),
  ('base','ent','country','subframe','2 6'),
  ('base','ent','crt_by','input','ent'),
  ('base','ent','crt_by','optional','1'),
  ('base','ent','crt_by','size','10'),
  ('base','ent','crt_by','state','readonly'),
  ('base','ent','crt_by','subframe','1 98'),
  ('base','ent','crt_by','write','0'),
  ('base','ent','crt_date','input','inf'),
  ('base','ent','crt_date','optional','1'),
  ('base','ent','crt_date','size','18'),
  ('base','ent','crt_date','state','readonly'),
  ('base','ent','crt_date','subframe','2 98'),
  ('base','ent','crt_date','write','0'),
  ('base','ent','ent_cmt','input','mle'),
  ('base','ent','ent_cmt','size','80'),
  ('base','ent','ent_cmt','special','edw'),
  ('base','ent','ent_cmt','subframe','1 7 3'),
  ('base','ent','ent_inact','initial','f'),
  ('base','ent','ent_inact','input','chk'),
  ('base','ent','ent_inact','offvalue','f'),
  ('base','ent','ent_inact','onvalue','t'),
  ('base','ent','ent_inact','size','2'),
  ('base','ent','ent_inact','subframe','3 3'),
  ('base','ent','ent_name','display','3'),
  ('base','ent','ent_name','focus','true'),
  ('base','ent','ent_name','input','ent'),
  ('base','ent','ent_name','size','40'),
  ('base','ent','ent_name','subframe','1 1 2'),
  ('base','ent','ent_name','template',E'^[\\w\\. ]+$'),
  ('base','ent','ent_type','display','2'),
  ('base','ent','ent_type','initial','p'),
  ('base','ent','ent_type','input','pdm'),
  ('base','ent','ent_type','size','2'),
  ('base','ent','ent_type','subframe','3 1'),
  ('base','ent','fir_name','background','#e0f0ff'),
  ('base','ent','fir_name','display','4'),
  ('base','ent','fir_name','input','ent'),
  ('base','ent','fir_name','size','14'),
  ('base','ent','fir_name','subframe','2 2'),
  ('base','ent','fir_name','template','alpha'),
  ('base','ent','gender','initial',''),
  ('base','ent','gender','input','pdm'),
  ('base','ent','gender','size','2'),
  ('base','ent','gender','subframe','2 4'),
  ('base','ent','id','display','1'),
  ('base','ent','id','hide','1'),
  ('base','ent','id','input','ent'),
  ('base','ent','id','justify','r'),
  ('base','ent','id','size','7'),
  ('base','ent','id','subframe','0 1'),
  ('base','ent','id','write','0'),
  ('base','ent','marital','initial',''),
  ('base','ent','marital','input','pdm'),
  ('base','ent','marital','size','2'),
  ('base','ent','marital','subframe','3 4'),
  ('base','ent','mid_name','input','ent'),
  ('base','ent','mid_name','size','12'),
  ('base','ent','mid_name','subframe','3 2'),
  ('base','ent','mid_name','template','alpha'),
  ('base','ent','mod_by','input','ent'),
  ('base','ent','mod_by','optional','1'),
  ('base','ent','mod_by','size','10'),
  ('base','ent','mod_by','state','readonly'),
  ('base','ent','mod_by','subframe','1 99'),
  ('base','ent','mod_by','write','0'),
  ('base','ent','mod_date','input','inf'),
  ('base','ent','mod_date','optional','1'),
  ('base','ent','mod_date','size','18'),
  ('base','ent','mod_date','state','readonly'),
  ('base','ent','mod_date','subframe','2 99'),
  ('base','ent','mod_date','write','0'),
  ('base','ent','pref_name','input','ent'),
  ('base','ent','pref_name','size','12'),
  ('base','ent','pref_name','subframe','1 3'),
  ('base','ent','pref_name','template','alpha'),
  ('base','ent','tax_id','hint','###-##-####'),
  ('base','ent','tax_id','input','ent'),
  ('base','ent','tax_id','size','10'),
  ('base','ent','tax_id','subframe','1 6'),
  ('base','ent','title','input','ent'),
  ('base','ent','title','size','8'),
  ('base','ent','title','special','exs'),
  ('base','ent','title','subframe','1 2'),
  ('base','ent','title','template',E'^[a-zA-Z\\.]*$'),
  ('base','ent','username','input','ent'),
  ('base','ent','username','size','12'),
  ('base','ent','username','subframe','2 5'),
  ('base','ent','username','template','alnum'),
  ('base','ent_link','mem','input','ent'),
  ('base','ent_link','mem','justify','r'),
  ('base','ent_link','mem','size','6'),
  ('base','ent_link','mem','subframe','1 2'),
  ('base','ent_link','org','input','ent'),
  ('base','ent_link','org','justify','r'),
  ('base','ent_link','org','size','6'),
  ('base','ent_link','org','subframe','1 1'),
  ('base','ent_link','org_id','focus','true'),
  ('base','ent_link','role','input','ent'),
  ('base','ent_link','role','size','30'),
  ('base','ent_link','role','special','exs'),
  ('base','ent_link','role','subframe','1 3'),
  ('base','ent_link_v','mem_name','depend','mem_id'),
  ('base','ent_link_v','mem_name','in','mem_id'),
  ('base','ent_link_v','mem_name','input','ent'),
  ('base','ent_link_v','mem_name','size','30'),
  ('base','ent_link_v','mem_name','subframe',''),
  ('base','ent_link_v','mem_name','title',':'),
  ('base','ent_link_v','org_name','depend','org_id'),
  ('base','ent_link_v','org_name','in','org_id'),
  ('base','ent_link_v','org_name','input','ent'),
  ('base','ent_link_v','org_name','size','30'),
  ('base','ent_link_v','org_name','subframe',''),
  ('base','ent_link_v','org_name','title',':'),
  ('base','ent_v','age','input','ent'),
  ('base','ent_v','age','optional','1'),
  ('base','ent_v','age','size','4'),
  ('base','ent_v','age','state','readonly'),
  ('base','ent_v','age','subframe','3 8'),
  ('base','ent_v','age','write','0'),
  ('base','ent_v','cas_name','input','ent'),
  ('base','ent_v','cas_name','optional','1'),
  ('base','ent_v','cas_name','size','10'),
  ('base','ent_v','cas_name','state','readonly'),
  ('base','ent_v','cas_name','subframe','1 9'),
  ('base','ent_v','cas_name','write','0'),
  ('base','ent_v','frm_name','input','ent'),
  ('base','ent_v','frm_name','optional','1'),
  ('base','ent_v','frm_name','size','18'),
  ('base','ent_v','frm_name','state','readonly'),
  ('base','ent_v','frm_name','subframe','2 8'),
  ('base','ent_v','frm_name','write','0'),
  ('base','ent_v','giv_name','input','ent'),
  ('base','ent_v','giv_name','optional','1'),
  ('base','ent_v','giv_name','size','10'),
  ('base','ent_v','giv_name','state','readonly'),
  ('base','ent_v','giv_name','subframe','2 9'),
  ('base','ent_v','giv_name','write','0'),
  ('base','ent_v','std_name','input','ent'),
  ('base','ent_v','std_name','optional','1'),
  ('base','ent_v','std_name','size','18'),
  ('base','ent_v','std_name','state','readonly'),
  ('base','ent_v','std_name','subframe','1 8'),
  ('base','ent_v','std_name','write','0'),
  ('base','ent_v_pub','activ','initial','t'),
  ('base','ent_v_pub','activ','input','chk'),
  ('base','ent_v_pub','activ','offvalue','f'),
  ('base','ent_v_pub','activ','onvalue','t'),
  ('base','ent_v_pub','activ','size','2'),
  ('base','ent_v_pub','activ','state','readonly'),
  ('base','ent_v_pub','activ','subframe','1 5'),
  ('base','ent_v_pub','crt_by','input','ent'),
  ('base','ent_v_pub','crt_by','optional','1'),
  ('base','ent_v_pub','crt_by','size','10'),
  ('base','ent_v_pub','crt_by','state','readonly'),
  ('base','ent_v_pub','crt_by','subframe','2 6'),
  ('base','ent_v_pub','crt_by','write','0'),
  ('base','ent_v_pub','crt_date','input','ent'),
  ('base','ent_v_pub','crt_date','optional','1'),
  ('base','ent_v_pub','crt_date','size','20'),
  ('base','ent_v_pub','crt_date','state','readonly'),
  ('base','ent_v_pub','crt_date','subframe','1 6'),
  ('base','ent_v_pub','crt_date','write','0'),
  ('base','ent_v_pub','ent_name','focus','true'),
  ('base','ent_v_pub','id','hide','1'),
  ('base','ent_v_pub','id','input','ent'),
  ('base','ent_v_pub','id','justify','r'),
  ('base','ent_v_pub','id','size','6'),
  ('base','ent_v_pub','id','subframe','0 1'),
  ('base','ent_v_pub','id','write','0'),
  ('base','ent_v_pub','mod_by','input','ent'),
  ('base','ent_v_pub','mod_by','optional','1'),
  ('base','ent_v_pub','mod_by','size','10'),
  ('base','ent_v_pub','mod_by','state','readonly'),
  ('base','ent_v_pub','mod_by','subframe','4 6'),
  ('base','ent_v_pub','mod_by','write','0'),
  ('base','ent_v_pub','mod_date','input','ent'),
  ('base','ent_v_pub','mod_date','optional','1'),
  ('base','ent_v_pub','mod_date','size','20'),
  ('base','ent_v_pub','mod_date','state','readonly'),
  ('base','ent_v_pub','mod_date','subframe','3 6'),
  ('base','ent_v_pub','mod_date','write','0'),
  ('base','ent_v_pub','name','input','ent'),
  ('base','ent_v_pub','name','size','40'),
  ('base','ent_v_pub','name','state','readonly'),
  ('base','ent_v_pub','name','subframe','1 1 2'),
  ('base','ent_v_pub','type','input','ent'),
  ('base','ent_v_pub','type','size','2'),
  ('base','ent_v_pub','type','state','readonly'),
  ('base','ent_v_pub','type','subframe','1 2'),
  ('base','ent_v_pub','username','input','ent'),
  ('base','ent_v_pub','username','size','12'),
  ('base','ent_v_pub','username','state','readonly'),
  ('base','ent_v_pub','username','subframe','2 2'),
  ('base','file_v','file_cks','display','2'),
  ('base','file_v','file_cmt','display','3'),
  ('base','file_v','file_prim','initial','false'),
  ('base','file_v','file_prim','input','chk'),
  ('base','file_v','file_prim','offvalue','f'),
  ('base','file_v','file_prim','onvalue','t'),
  ('base','file_v','file_prim','size','2'),
  ('base','file_v','file_prim','state','readonly'),
  ('base','file_v','file_prim','subframe','3 2'),
  ('base','file_v','file_prim','write','0'),
  ('base','file_v','file_seq','display','4'),
  ('base','file_v','file_seq','sort','2'),
  ('base','file_v','file_type','display','1'),
  ('base','file_v','file_type','sort','1'),
  ('base','file_v','std_name','depend','file_ent'),
  ('base','file_v','std_name','in','file_ent'),
  ('base','file_v','std_name','input','ent'),
  ('base','file_v','std_name','optional','1'),
  ('base','file_v','std_name','size','14'),
  ('base','file_v','std_name','subframe','2 5 2'),
  ('base','file_v','std_name','title',':'),
  ('base','parm_v','cmt','display','5'),
  ('base','parm_v','cmt','input','ent'),
  ('base','parm_v','cmt','size','50'),
  ('base','parm_v','cmt','special','edw'),
  ('base','parm_v','cmt','subframe','1 3 2'),
  ('base','parm_v','crt_by','input','ent'),
  ('base','parm_v','crt_by','optional','1'),
  ('base','parm_v','crt_by','size','10'),
  ('base','parm_v','crt_by','state','readonly'),
  ('base','parm_v','crt_by','subframe','1 98'),
  ('base','parm_v','crt_by','write','0'),
  ('base','parm_v','crt_date','input','inf'),
  ('base','parm_v','crt_date','optional','1'),
  ('base','parm_v','crt_date','size','18'),
  ('base','parm_v','crt_date','state','readonly'),
  ('base','parm_v','crt_date','subframe','2 98'),
  ('base','parm_v','crt_date','write','0'),
  ('base','parm_v','mod_by','input','ent'),
  ('base','parm_v','mod_by','optional','1'),
  ('base','parm_v','mod_by','size','10'),
  ('base','parm_v','mod_by','state','readonly'),
  ('base','parm_v','mod_by','subframe','1 99'),
  ('base','parm_v','mod_by','write','0'),
  ('base','parm_v','mod_date','input','inf'),
  ('base','parm_v','mod_date','optional','1'),
  ('base','parm_v','mod_date','size','18'),
  ('base','parm_v','mod_date','state','readonly'),
  ('base','parm_v','mod_date','subframe','2 99'),
  ('base','parm_v','mod_date','write','0'),
  ('base','parm_v','module','display','1'),
  ('base','parm_v','module','focus','true'),
  ('base','parm_v','module','input','ent'),
  ('base','parm_v','module','size','12'),
  ('base','parm_v','module','special','exs'),
  ('base','parm_v','module','subframe','1 1'),
  ('base','parm_v','parm','display','2'),
  ('base','parm_v','parm','input','ent'),
  ('base','parm_v','parm','size','24'),
  ('base','parm_v','parm','subframe','2 1'),
  ('base','parm_v','type','display','3'),
  ('base','parm_v','type','initial','text'),
  ('base','parm_v','type','input','pdm'),
  ('base','parm_v','type','size','6'),
  ('base','parm_v','type','subframe','1 2'),
  ('base','parm_v','value','display','4'),
  ('base','parm_v','value','hot','1'),
  ('base','parm_v','value','input','ent'),
  ('base','parm_v','value','size','24'),
  ('base','parm_v','value','special','edw'),
  ('base','parm_v','value','subframe','2 2'),
  ('base','priv','cmt','input','ent'),
  ('base','priv','cmt','size','30'),
  ('base','priv','cmt','subframe','1 1 2'),
  ('base','priv','grantee','input','ent'),
  ('base','priv','grantee','size','12'),
  ('base','priv','grantee','state','readonly'),
  ('base','priv','grantee','subframe','0 0'),
  ('base','priv','level','initial','2'),
  ('base','priv','level','input','ent'),
  ('base','priv','level','justify','r'),
  ('base','priv','level','size','4'),
  ('base','priv','level','subframe','2 0'),
  ('base','priv','priv','focus','true'),
  ('base','priv','priv','input','ent'),
  ('base','priv','priv','size','12'),
  ('base','priv','priv','special','exs'),
  ('base','priv','priv','subframe','1 0'),
  ('base','priv','priv_level','input','ent'),
  ('base','priv','priv_level','size','10'),
  ('base','priv','priv_level','state','readonly'),
  ('base','priv','priv_level','subframe','0 1'),
  ('base','priv','priv_level','write','0'),
  ('base','priv_v','priv_list','input','ent'),
  ('base','priv_v','priv_list','optional','1'),
  ('base','priv_v','priv_list','size','48'),
  ('base','priv_v','priv_list','state','disabled'),
  ('base','priv_v','priv_list','subframe','1 2 2'),
  ('base','priv_v','priv_list','write','0'),
  ('base','priv_v','std_name','input','ent'),
  ('base','priv_v','std_name','optional','1'),
  ('base','priv_v','std_name','size','24'),
  ('base','priv_v','std_name','state','disabled'),
  ('base','priv_v','std_name','subframe','0 2'),
  ('base','priv_v','std_name','write','0'),
  ('mychips','chits','chit_ent','size','6'),
  ('mychips','chits','chit_idx','size','4'),
  ('mychips','chits','chit_seq','size','4'),
  ('mychips','chits','units','size','10'),
  ('mychips','chits_v','chit_ent','display','1'),
  ('mychips','chits_v','chit_idx','display','3'),
  ('mychips','chits_v','chit_seq','display','2'),
  ('mychips','chits_v','chit_type','display','4'),
  ('mychips','chits_v','units','display','5'),
  ('mychips','chits_v_me','chit_ent','display','1'),
  ('mychips','chits_v_me','chit_idx','display','3'),
  ('mychips','chits_v_me','chit_seq','display','2'),
  ('mychips','chits_v_me','chit_type','display','4'),
  ('mychips','chits_v_me','units','display','5'),
  ('mychips','contracts','crt_by','input','ent'),
  ('mychips','contracts','crt_by','optional','1'),
  ('mychips','contracts','crt_by','size','10'),
  ('mychips','contracts','crt_by','state','readonly'),
  ('mychips','contracts','crt_by','subframe','1 98'),
  ('mychips','contracts','crt_by','write','0'),
  ('mychips','contracts','crt_date','input','inf'),
  ('mychips','contracts','crt_date','optional','1'),
  ('mychips','contracts','crt_date','size','18'),
  ('mychips','contracts','crt_date','state','readonly'),
  ('mychips','contracts','crt_date','subframe','2 98'),
  ('mychips','contracts','crt_date','write','0'),
  ('mychips','contracts','digest','input','ent'),
  ('mychips','contracts','digest','size','20'),
  ('mychips','contracts','digest','state','readonly'),
  ('mychips','contracts','digest','subframe','3 4'),
  ('mychips','contracts','digest','write','0'),
  ('mychips','contracts','domain','display','1'),
  ('mychips','contracts','domain','focus','true'),
  ('mychips','contracts','domain','input','ent'),
  ('mychips','contracts','domain','size','20'),
  ('mychips','contracts','domain','subframe','1 1'),
  ('mychips','contracts','language','display','4'),
  ('mychips','contracts','language','input','ent'),
  ('mychips','contracts','language','size','4'),
  ('mychips','contracts','language','subframe','3 2'),
  ('mychips','contracts','mod_by','input','ent'),
  ('mychips','contracts','mod_by','optional','1'),
  ('mychips','contracts','mod_by','size','10'),
  ('mychips','contracts','mod_by','state','readonly'),
  ('mychips','contracts','mod_by','subframe','1 99'),
  ('mychips','contracts','mod_by','write','0'),
  ('mychips','contracts','mod_date','input','inf'),
  ('mychips','contracts','mod_date','optional','1'),
  ('mychips','contracts','mod_date','size','18'),
  ('mychips','contracts','mod_date','state','readonly'),
  ('mychips','contracts','mod_date','subframe','2 99'),
  ('mychips','contracts','mod_date','write','0'),
  ('mychips','contracts','name','display','2'),
  ('mychips','contracts','name','input','ent'),
  ('mychips','contracts','name','size','30'),
  ('mychips','contracts','name','subframe','1 2 2'),
  ('mychips','contracts','published','input','ent'),
  ('mychips','contracts','published','size','14'),
  ('mychips','contracts','published','state','readonly'),
  ('mychips','contracts','published','subframe','3 1'),
  ('mychips','contracts','published','write','0'),
  ('mychips','contracts','sections','hide','1'),
  ('mychips','contracts','sections','input','ent'),
  ('mychips','contracts','sections','size','80'),
  ('mychips','contracts','sections','state','readonly'),
  ('mychips','contracts','sections','subframe',''),
  ('mychips','contracts','tag','input','ent'),
  ('mychips','contracts','tag','size','10'),
  ('mychips','contracts','tag','subframe','3 3'),
  ('mychips','contracts','text','input','mle'),
  ('mychips','contracts','text','size','80'),
  ('mychips','contracts','text','special','edw'),
  ('mychips','contracts','text','subframe','1 5 4'),
  ('mychips','contracts','title','display','7'),
  ('mychips','contracts','title','input','ent'),
  ('mychips','contracts','title','size','40'),
  ('mychips','contracts','title','special','edw'),
  ('mychips','contracts','title','subframe','1 3 2'),
  ('mychips','contracts','version','display','3'),
  ('mychips','contracts','version','input','ent'),
  ('mychips','contracts','version','justify','r'),
  ('mychips','contracts','version','size','3'),
  ('mychips','contracts','version','subframe','2 1'),
  ('mychips','contracts_v','json','input','mle'),
  ('mychips','contracts_v','json','optional','1'),
  ('mychips','contracts_v','json','size','80 6'),
  ('mychips','contracts_v','json','special','edw'),
  ('mychips','contracts_v','json','state','readonly'),
  ('mychips','contracts_v','json','subframe','1 8 4'),
  ('mychips','contracts_v','source','input','ent'),
  ('mychips','contracts_v','source','size','20'),
  ('mychips','contracts_v','source','state','readonly'),
  ('mychips','contracts_v','source','subframe','1 4 2'),
  ('mychips','routes','dest_chid','size','16'),
  ('mychips','routes','dest_ent','size','7'),
  ('mychips','routes','dest_host','size','18'),
  ('mychips','routes','route_ent','size','7'),
  ('mychips','routes','status','display','5'),
  ('mychips','routes_v','dest_addr','size','30'),
  ('mychips','routes_v','route_addr','size','30'),
  ('mychips','routes_v','status','display','5'),
  ('mychips','tallies','bound','input','ent'),
  ('mychips','tallies','bound','size','8'),
  ('mychips','tallies','bound','subframe','3 9'),
  ('mychips','tallies','clutch','input','ent'),
  ('mychips','tallies','clutch','size','8'),
  ('mychips','tallies','clutch','subframe','2 9'),
  ('mychips','tallies','comment','input','ent'),
  ('mychips','tallies','comment','size','40'),
  ('mychips','tallies','comment','subframe','0 5 4'),
  ('mychips','tallies','contract','input','ent'),
  ('mychips','tallies','contract','size','20'),
  ('mychips','tallies','contract','subframe','0 6 4'),
  ('mychips','tallies','cr_limit','input','ent'),
  ('mychips','tallies','cr_limit','size','12'),
  ('mychips','tallies','cr_limit','subframe','1 10'),
  ('mychips','tallies','crt_by','input','ent'),
  ('mychips','tallies','crt_by','optional','1'),
  ('mychips','tallies','crt_by','size','10'),
  ('mychips','tallies','crt_by','state','readonly'),
  ('mychips','tallies','crt_by','subframe','1 98'),
  ('mychips','tallies','crt_by','write','0'),
  ('mychips','tallies','crt_date','input','inf'),
  ('mychips','tallies','crt_date','optional','1'),
  ('mychips','tallies','crt_date','size','18'),
  ('mychips','tallies','crt_date','state','readonly'),
  ('mychips','tallies','crt_date','subframe','2 98'),
  ('mychips','tallies','crt_date','write','0'),
  ('mychips','tallies','dr_limit','input','ent'),
  ('mychips','tallies','dr_limit','size','12'),
  ('mychips','tallies','dr_limit','subframe','0 10'),
  ('mychips','tallies','foil_terms','input','mle'),
  ('mychips','tallies','foil_terms','size','80 2'),
  ('mychips','tallies','foil_terms','subframe','0 8 4'),
  ('mychips','tallies','hold_sig','input','ent'),
  ('mychips','tallies','hold_sig','size','20'),
  ('mychips','tallies','hold_sig','subframe','1 4 2'),
  ('mychips','tallies','mod_by','input','ent'),
  ('mychips','tallies','mod_by','optional','1'),
  ('mychips','tallies','mod_by','size','10'),
  ('mychips','tallies','mod_by','state','readonly'),
  ('mychips','tallies','mod_by','subframe','1 99'),
  ('mychips','tallies','mod_by','write','0'),
  ('mychips','tallies','mod_date','input','inf'),
  ('mychips','tallies','mod_date','optional','1'),
  ('mychips','tallies','mod_date','size','18'),
  ('mychips','tallies','mod_date','state','readonly'),
  ('mychips','tallies','mod_date','subframe','2 99'),
  ('mychips','tallies','mod_date','write','0'),
  ('mychips','tallies','part_ent','display','5'),
  ('mychips','tallies','part_ent','input','ent'),
  ('mychips','tallies','part_ent','size','8'),
  ('mychips','tallies','part_ent','subframe','2 2'),
  ('mychips','tallies','part_sig','input','ent'),
  ('mychips','tallies','part_sig','size','20'),
  ('mychips','tallies','part_sig','subframe','3 4 2'),
  ('mychips','tallies','request','input','ent'),
  ('mychips','tallies','request','size','10'),
  ('mychips','tallies','request','subframe','1 3'),
  ('mychips','tallies','reward','display','10'),
  ('mychips','tallies','reward','input','ent'),
  ('mychips','tallies','reward','size','8'),
  ('mychips','tallies','reward','subframe','1 9'),
  ('mychips','tallies','status','display','4'),
  ('mychips','tallies','status','input','ent'),
  ('mychips','tallies','status','size','10'),
  ('mychips','tallies','status','subframe','0 3'),
  ('mychips','tallies','stock_terms','input','mle'),
  ('mychips','tallies','stock_terms','size','80 2'),
  ('mychips','tallies','stock_terms','subframe','0 7 2'),
  ('mychips','tallies','tally_date','display','6'),
  ('mychips','tallies','tally_date','input','ent'),
  ('mychips','tallies','tally_date','size','20'),
  ('mychips','tallies','tally_date','subframe','1 2'),
  ('mychips','tallies','tally_ent','display','1'),
  ('mychips','tallies','tally_ent','hide','1'),
  ('mychips','tallies','tally_ent','input','ent'),
  ('mychips','tallies','tally_ent','size','6'),
  ('mychips','tallies','tally_ent','sort','1'),
  ('mychips','tallies','tally_ent','subframe','0 15'),
  ('mychips','tallies','tally_ent','write','0'),
  ('mychips','tallies','tally_seq','display','2'),
  ('mychips','tallies','tally_seq','hide','1'),
  ('mychips','tallies','tally_seq','input','ent'),
  ('mychips','tallies','tally_seq','size','4'),
  ('mychips','tallies','tally_seq','subframe','1 15'),
  ('mychips','tallies','tally_type','display','3'),
  ('mychips','tallies','tally_type','input','ent'),
  ('mychips','tallies','tally_type','size','6'),
  ('mychips','tallies','tally_type','subframe','0 1'),
  ('mychips','tallies','tally_uuid','display','7'),
  ('mychips','tallies','tally_uuid','input','ent'),
  ('mychips','tallies','tally_uuid','size','40'),
  ('mychips','tallies','tally_uuid','subframe','0 2'),
  ('mychips','tallies','target','display','11'),
  ('mychips','tallies','target','input','ent'),
  ('mychips','tallies','target','size','8'),
  ('mychips','tallies','target','subframe','0 9'),
  ('mychips','tallies','units','input','ent'),
  ('mychips','tallies','units','size','16'),
  ('mychips','tallies','units','subframe','2 10'),
  ('mychips','tallies','version','input','ent'),
  ('mychips','tallies','version','size','40'),
  ('mychips','tallies','version','subframe','1 1'),
  ('mychips','tallies_v','part_cid','input','ent'),
  ('mychips','tallies_v','part_cid','optional','1'),
  ('mychips','tallies_v','part_cid','size','28'),
  ('mychips','tallies_v','part_cid','state','readonly'),
  ('mychips','tallies_v','part_cid','subframe','3 16'),
  ('mychips','tallies_v','part_cid','write','0'),
  ('mychips','tallies_v','part_ent','display','5'),
  ('mychips','tallies_v','part_name','input','ent'),
  ('mychips','tallies_v','part_name','optional','1'),
  ('mychips','tallies_v','part_name','size','28'),
  ('mychips','tallies_v','part_name','state','readonly'),
  ('mychips','tallies_v','part_name','subframe','3 16'),
  ('mychips','tallies_v','part_name','write','0'),
  ('mychips','tallies_v','part_sock','input','ent'),
  ('mychips','tallies_v','part_sock','optional','1'),
  ('mychips','tallies_v','part_sock','size','28'),
  ('mychips','tallies_v','part_sock','state','readonly'),
  ('mychips','tallies_v','part_sock','subframe','3 16'),
  ('mychips','tallies_v','part_sock','write','0'),
  ('mychips','tallies_v','reward','display','7'),
  ('mychips','tallies_v','status','display','4'),
  ('mychips','tallies_v','tally_ent','display','1'),
  ('mychips','tallies_v','tally_seq','display','2'),
  ('mychips','tallies_v','tally_type','display','3'),
  ('mychips','tallies_v','target','display','10'),
  ('mychips','tallies_v','user_cid','input','ent'),
  ('mychips','tallies_v','user_cid','optional','1'),
  ('mychips','tallies_v','user_cid','size','28'),
  ('mychips','tallies_v','user_cid','state','readonly'),
  ('mychips','tallies_v','user_cid','subframe','3 14'),
  ('mychips','tallies_v','user_cid','write','0'),
  ('mychips','tallies_v','user_name','input','ent'),
  ('mychips','tallies_v','user_name','optional','1'),
  ('mychips','tallies_v','user_name','size','28'),
  ('mychips','tallies_v','user_name','state','readonly'),
  ('mychips','tallies_v','user_name','subframe','3 14'),
  ('mychips','tallies_v','user_name','write','0'),
  ('mychips','tallies_v','user_sock','input','ent'),
  ('mychips','tallies_v','user_sock','optional','1'),
  ('mychips','tallies_v','user_sock','size','28'),
  ('mychips','tallies_v','user_sock','state','readonly'),
  ('mychips','tallies_v','user_sock','subframe','3 14'),
  ('mychips','tallies_v','user_sock','write','0'),
  ('mychips','tallies_v_me','part_ent','display','4'),
  ('mychips','tallies_v_me','tally_ent','display','1'),
  ('mychips','tallies_v_me','tally_seq','display','2'),
  ('mychips','tallies_v_me','tally_type','display','3'),
  ('mychips','tallies_v_paths','bang','display','1'),
  ('mychips','tallies_v_paths','bang','size','10'),
  ('mychips','tallies_v_paths','circuit','display','5'),
  ('mychips','tallies_v_paths','circuit','size','5'),
  ('mychips','tallies_v_paths','length','size','4'),
  ('mychips','tallies_v_paths','max','display','4'),
  ('mychips','tallies_v_paths','max','size','10'),
  ('mychips','tallies_v_paths','min','display','3'),
  ('mychips','tallies_v_paths','min','size','10'),
  ('mychips','tallies_v_paths','path','display','6'),
  ('mychips','tallies_v_paths','path','size','120'),
  ('mychips','users','crt_by','input','ent'),
  ('mychips','users','crt_by','optional','1'),
  ('mychips','users','crt_by','size','10'),
  ('mychips','users','crt_by','state','readonly'),
  ('mychips','users','crt_by','subframe','1 98'),
  ('mychips','users','crt_by','write','0'),
  ('mychips','users','crt_date','input','inf'),
  ('mychips','users','crt_date','optional','1'),
  ('mychips','users','crt_date','size','18'),
  ('mychips','users','crt_date','state','readonly'),
  ('mychips','users','crt_date','subframe','2 98'),
  ('mychips','users','crt_date','write','0'),
  ('mychips','users','ent_name','focus','true'),
  ('mychips','users','mod_by','input','ent'),
  ('mychips','users','mod_by','optional','1'),
  ('mychips','users','mod_by','size','10'),
  ('mychips','users','mod_by','state','readonly'),
  ('mychips','users','mod_by','subframe','1 99'),
  ('mychips','users','mod_by','write','0'),
  ('mychips','users','mod_date','input','inf'),
  ('mychips','users','mod_date','optional','1'),
  ('mychips','users','mod_date','size','18'),
  ('mychips','users','mod_date','state','readonly'),
  ('mychips','users','mod_date','subframe','2 99'),
  ('mychips','users','mod_date','write','0'),
  ('mychips','users','user_cmt','input','mle'),
  ('mychips','users','user_cmt','size','80 2'),
  ('mychips','users','user_cmt','subframe','1 12 4'),
  ('mychips','users','user_ent','hide','1'),
  ('mychips','users','user_ent','input','ent'),
  ('mychips','users','user_ent','size','6'),
  ('mychips','users','user_ent','sort','1'),
  ('mychips','users','user_ent','subframe','0 10'),
  ('mychips','users','user_ent','write','0'),
  ('mychips','users','user_hid','input','ent'),
  ('mychips','users','user_hid','size','20'),
  ('mychips','users','user_hid','subframe','3 11'),
  ('mychips','users','user_host','input','ent'),
  ('mychips','users','user_host','size','20'),
  ('mychips','users','user_host','subframe','1 11'),
  ('mychips','users','user_port','input','ent'),
  ('mychips','users','user_port','justify','r'),
  ('mychips','users','user_port','size','8'),
  ('mychips','users','user_port','subframe','2 11'),
  ('mychips','users','user_stat','initial','act'),
  ('mychips','users','user_stat','input','pdm'),
  ('mychips','users','user_stat','size','10'),
  ('mychips','users','user_stat','subframe','1 10'),
  ('mychips','users_v','born_date','display','6'),
  ('mychips','users_v','ent_name','display','0'),
  ('mychips','users_v','ent_type','display','3'),
  ('mychips','users_v','fir_name','display','0'),
  ('mychips','users_v','id','display','1'),
  ('mychips','users_v','peer_sock','input','ent'),
  ('mychips','users_v','peer_sock','optional','1'),
  ('mychips','users_v','peer_sock','size','28'),
  ('mychips','users_v','peer_sock','state','readonly'),
  ('mychips','users_v','peer_sock','subframe','3 21'),
  ('mychips','users_v','peer_sock','write','0'),
  ('mychips','users_v','std_name','display','2'),
  ('mychips','users_v','user_sock','input','ent'),
  ('mychips','users_v','user_sock','optional','1'),
  ('mychips','users_v','user_sock','size','28'),
  ('mychips','users_v','user_sock','state','readonly'),
  ('mychips','users_v','user_sock','subframe','3 11'),
  ('mychips','users_v','user_sock','write','0'),
  ('mychips','users_v','user_stat','display','4'),
  ('mychips','users_v_flat','bill_addr','display','4'),
  ('mychips','users_v_flat','bill_city','display','5'),
  ('mychips','users_v_flat','bill_state','display','6'),
  ('mychips','users_v_flat','id','display','1'),
  ('mychips','users_v_flat','id','sort','2'),
  ('mychips','users_v_flat','std_name','display','3'),
  ('mychips','users_v_flat','std_name','sort','1'),
  ('wm','column_pub','code','focus','true'),
  ('wm','column_pub','help','size','40'),
  ('wm','column_pub','help','special','edw'),
  ('wm','column_pub','language','size','4'),
  ('wm','column_pub','title','size','40'),
  ('wm','column_text','code','focus','true'),
  ('wm','column_text','help','size','40'),
  ('wm','column_text','help','special','edw'),
  ('wm','column_text','language','size','4'),
  ('wm','column_text','title','size','40'),
  ('wm','message_text','code','focus','true'),
  ('wm','message_text','help','size','40'),
  ('wm','message_text','help','special','edw'),
  ('wm','message_text','language','size','4'),
  ('wm','message_text','title','size','40'),
  ('wm','objects','build','size','4'),
  ('wm','objects','built','size','4'),
  ('wm','objects','checkit','size','4'),
  ('wm','objects','col_data','size','40'),
  ('wm','objects','col_data','special','edw'),
  ('wm','objects','crt_sql','size','40'),
  ('wm','objects','crt_sql','special','edw'),
  ('wm','objects','deps','size','40'),
  ('wm','objects','deps','special','edw'),
  ('wm','objects','drp_sql','size','40'),
  ('wm','objects','drp_sql','special','edw'),
  ('wm','objects','grants','size','40'),
  ('wm','objects','grants','special','edw'),
  ('wm','objects','max_rel','size','4'),
  ('wm','objects','min_rel','size','4'),
  ('wm','objects','mod_ver','size','4'),
  ('wm','objects','name','size','40'),
  ('wm','objects','ndeps','size','40'),
  ('wm','objects','ndeps','special','edw'),
  ('wm','objects','obj_nam','focus','true'),
  ('wm','table_text','code','focus','true'),
  ('wm','table_text','help','size','40'),
  ('wm','table_text','help','special','edw'),
  ('wm','table_text','language','size','4'),
  ('wm','table_text','title','size','40'),
  ('wm','value_text','code','focus','true'),
  ('wm','value_text','help','size','40'),
  ('wm','value_text','help','special','edw'),
  ('wm','value_text','language','size','4'),
  ('wm','value_text','title','size','40'),
  ('wylib','data','access','display','6'),
  ('wylib','data','access','input','ent'),
  ('wylib','data','access','size','6'),
  ('wylib','data','access','subframe','2 3'),
  ('wylib','data','component','display','2'),
  ('wylib','data','component','input','ent'),
  ('wylib','data','component','size','20'),
  ('wylib','data','component','subframe','2 1'),
  ('wylib','data','crt_by','input','ent'),
  ('wylib','data','crt_by','optional','1'),
  ('wylib','data','crt_by','size','14'),
  ('wylib','data','crt_by','state','disabled'),
  ('wylib','data','crt_by','subframe','1 6'),
  ('wylib','data','crt_date','input','ent'),
  ('wylib','data','crt_date','optional','1'),
  ('wylib','data','crt_date','size','14'),
  ('wylib','data','crt_date','state','disabled'),
  ('wylib','data','crt_date','subframe','1 6'),
  ('wylib','data','data','input','mle'),
  ('wylib','data','data','size','80'),
  ('wylib','data','data','state','disabled'),
  ('wylib','data','data','subframe','1 4 3'),
  ('wylib','data','descr','display','4'),
  ('wylib','data','descr','input','ent'),
  ('wylib','data','descr','size','40'),
  ('wylib','data','descr','subframe','4 2 3'),
  ('wylib','data','mod_by','input','ent'),
  ('wylib','data','mod_by','optional','1'),
  ('wylib','data','mod_by','size','14'),
  ('wylib','data','mod_by','state','disabled'),
  ('wylib','data','mod_by','subframe','2 7'),
  ('wylib','data','mod_date','input','ent'),
  ('wylib','data','mod_date','optional','1'),
  ('wylib','data','mod_date','size','14'),
  ('wylib','data','mod_date','state','disabled'),
  ('wylib','data','mod_date','subframe','2 7'),
  ('wylib','data','name','display','3'),
  ('wylib','data','name','input','ent'),
  ('wylib','data','name','size','16'),
  ('wylib','data','name','subframe','3 1 2'),
  ('wylib','data','owner','display','5'),
  ('wylib','data','owner','input','ent'),
  ('wylib','data','owner','size','4'),
  ('wylib','data','owner','subframe','1 3'),
  ('wylib','data','ruid','display','1'),
  ('wylib','data','ruid','hide','1'),
  ('wylib','data','ruid','input','ent'),
  ('wylib','data','ruid','size','3'),
  ('wylib','data','ruid','state','disabled'),
  ('wylib','data','ruid','subframe','1 1'),
  ('wylib','data_v','access','display','6'),
  ('wylib','data_v','component','display','2'),
  ('wylib','data_v','descr','display','4'),
  ('wylib','data_v','name','display','3'),
  ('wylib','data_v','own_name','display','5'),
  ('wylib','data_v','own_name','input','ent'),
  ('wylib','data_v','own_name','size','14'),
  ('wylib','data_v','own_name','subframe','4 3'),
  ('wylib','data_v','ruid','display','1');
insert into wm.column_native (cnt_sch,cnt_tab,cnt_col,nat_sch,nat_tab,nat_col,nat_exp,pkey) values
  ('base','addr','addr_cmt','base','addr','addr_cmt','f','f'),
  ('base','addr','addr_ent','base','addr','addr_ent','f','t'),
  ('base','addr','addr_inact','base','addr','addr_inact','f','f'),
  ('base','addr','addr_prim','base','addr','addr_prim','f','f'),
  ('base','addr','addr_priv','base','addr','addr_priv','f','f'),
  ('base','addr','addr_seq','base','addr','addr_seq','f','t'),
  ('base','addr','addr_spec','base','addr','addr_spec','f','f'),
  ('base','addr','addr_type','base','addr','addr_type','f','f'),
  ('base','addr','city','base','addr','city','f','f'),
  ('base','addr','country','base','addr','country','f','f'),
  ('base','addr','crt_by','base','addr','crt_by','f','f'),
  ('base','addr','crt_date','base','addr','crt_date','f','f'),
  ('base','addr','mod_by','base','addr','mod_by','f','f'),
  ('base','addr','mod_date','base','addr','mod_date','f','f'),
  ('base','addr','pcode','base','addr','pcode','f','f'),
  ('base','addr','state','base','addr','state','f','f'),
  ('base','addr_prim','prim_ent','base','addr_prim','prim_ent','f','t'),
  ('base','addr_prim','prim_seq','base','addr_prim','prim_seq','f','t'),
  ('base','addr_prim','prim_type','base','addr_prim','prim_type','f','t'),
  ('base','addr_v','addr_cmt','base','addr','addr_cmt','f','f'),
  ('base','addr_v','addr_ent','base','addr','addr_ent','f','t'),
  ('base','addr_v','addr_inact','base','addr','addr_inact','f','f'),
  ('base','addr_v','addr_prim','base','addr_v','addr_prim','f','f'),
  ('base','addr_v','addr_priv','base','addr','addr_priv','f','f'),
  ('base','addr_v','addr_seq','base','addr','addr_seq','f','t'),
  ('base','addr_v','addr_spec','base','addr','addr_spec','f','f'),
  ('base','addr_v','addr_type','base','addr','addr_type','f','f'),
  ('base','addr_v','city','base','addr','city','f','f'),
  ('base','addr_v','country','base','addr','country','f','f'),
  ('base','addr_v','crt_by','base','addr','crt_by','f','f'),
  ('base','addr_v','crt_date','base','addr','crt_date','f','f'),
  ('base','addr_v','mod_by','base','addr','mod_by','f','f'),
  ('base','addr_v','mod_date','base','addr','mod_date','f','f'),
  ('base','addr_v','pcode','base','addr','pcode','f','f'),
  ('base','addr_v','state','base','addr','state','f','f'),
  ('base','addr_v','std_name','base','ent_v','std_name','f','f'),
  ('base','addr_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('base','addr_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('base','addr_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('base','addr_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('base','addr_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('base','addr_v_flat','birth_addr','base','addr_v_flat','birth_addr','f','f'),
  ('base','addr_v_flat','birth_city','base','addr_v_flat','birth_city','f','f'),
  ('base','addr_v_flat','birth_country','base','addr_v_flat','birth_country','f','f'),
  ('base','addr_v_flat','birth_pcode','base','addr_v_flat','birth_pcode','f','f'),
  ('base','addr_v_flat','birth_state','base','addr_v_flat','birth_state','f','f'),
  ('base','addr_v_flat','id','base','ent','id','f','t'),
  ('base','addr_v_flat','mail_addr','base','addr_v_flat','mail_addr','f','f'),
  ('base','addr_v_flat','mail_city','base','addr_v_flat','mail_city','f','f'),
  ('base','addr_v_flat','mail_country','base','addr_v_flat','mail_country','f','f'),
  ('base','addr_v_flat','mail_pcode','base','addr_v_flat','mail_pcode','f','f'),
  ('base','addr_v_flat','mail_state','base','addr_v_flat','mail_state','f','f'),
  ('base','addr_v_flat','phys_addr','base','addr_v_flat','phys_addr','f','f'),
  ('base','addr_v_flat','phys_city','base','addr_v_flat','phys_city','f','f'),
  ('base','addr_v_flat','phys_country','base','addr_v_flat','phys_country','f','f'),
  ('base','addr_v_flat','phys_pcode','base','addr_v_flat','phys_pcode','f','f'),
  ('base','addr_v_flat','phys_state','base','addr_v_flat','phys_state','f','f'),
  ('base','addr_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('base','addr_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('base','addr_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('base','addr_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('base','addr_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('base','comm','comm_cmt','base','comm','comm_cmt','f','f'),
  ('base','comm','comm_ent','base','comm','comm_ent','f','t'),
  ('base','comm','comm_inact','base','comm','comm_inact','f','f'),
  ('base','comm','comm_prim','base','comm','comm_prim','f','f'),
  ('base','comm','comm_priv','base','comm','comm_priv','f','f'),
  ('base','comm','comm_seq','base','comm','comm_seq','f','t'),
  ('base','comm','comm_spec','base','comm','comm_spec','f','f'),
  ('base','comm','comm_type','base','comm','comm_type','f','f'),
  ('base','comm','crt_by','base','comm','crt_by','f','f'),
  ('base','comm','crt_date','base','comm','crt_date','f','f'),
  ('base','comm','mod_by','base','comm','mod_by','f','f'),
  ('base','comm','mod_date','base','comm','mod_date','f','f'),
  ('base','comm_prim','prim_ent','base','comm_prim','prim_ent','f','t'),
  ('base','comm_prim','prim_seq','base','comm_prim','prim_seq','f','t'),
  ('base','comm_prim','prim_type','base','comm_prim','prim_type','f','t'),
  ('base','comm_v','comm_cmt','base','comm','comm_cmt','f','f'),
  ('base','comm_v','comm_ent','base','comm','comm_ent','f','t'),
  ('base','comm_v','comm_inact','base','comm','comm_inact','f','f'),
  ('base','comm_v','comm_prim','base','comm_v','comm_prim','f','f'),
  ('base','comm_v','comm_priv','base','comm','comm_priv','f','f'),
  ('base','comm_v','comm_seq','base','comm','comm_seq','f','t'),
  ('base','comm_v','comm_spec','base','comm','comm_spec','f','f'),
  ('base','comm_v','comm_type','base','comm','comm_type','f','f'),
  ('base','comm_v','crt_by','base','comm','crt_by','f','f'),
  ('base','comm_v','crt_date','base','comm','crt_date','f','f'),
  ('base','comm_v','mod_by','base','comm','mod_by','f','f'),
  ('base','comm_v','mod_date','base','comm','mod_date','f','f'),
  ('base','comm_v','std_name','base','ent_v','std_name','f','f'),
  ('base','comm_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('base','comm_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('base','comm_v_flat','fax_comm','base','comm_v_flat','fax_comm','f','f'),
  ('base','comm_v_flat','id','base','ent','id','f','t'),
  ('base','comm_v_flat','other_comm','base','comm_v_flat','other_comm','f','f'),
  ('base','comm_v_flat','pager_comm','base','comm_v_flat','pager_comm','f','f'),
  ('base','comm_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('base','comm_v_flat','text_comm','base','comm_v_flat','text_comm','f','f'),
  ('base','comm_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('base','country','capital','base','country','capital','f','f'),
  ('base','country','code','base','country','code','f','t'),
  ('base','country','com_name','base','country','com_name','f','f'),
  ('base','country','cur_code','base','country','cur_code','f','f'),
  ('base','country','cur_name','base','country','cur_name','f','f'),
  ('base','country','dial_code','base','country','dial_code','f','f'),
  ('base','country','iana','base','country','iana','f','f'),
  ('base','country','iso_3','base','country','iso_3','f','f'),
  ('base','ent','_last_addr','base','ent','_last_addr','f','f'),
  ('base','ent','_last_comm','base','ent','_last_comm','f','f'),
  ('base','ent','bank','base','ent','bank','f','f'),
  ('base','ent','born_date','base','ent','born_date','f','f'),
  ('base','ent','conn_pub','base','ent','conn_pub','f','f'),
  ('base','ent','country','base','ent','country','f','f'),
  ('base','ent','crt_by','base','ent','crt_by','f','f'),
  ('base','ent','crt_date','base','ent','crt_date','f','f'),
  ('base','ent','ent_cmt','base','ent','ent_cmt','f','f'),
  ('base','ent','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent','ent_name','base','ent','ent_name','f','f'),
  ('base','ent','ent_num','base','ent','ent_num','f','f'),
  ('base','ent','ent_type','base','ent','ent_type','f','f'),
  ('base','ent','fir_name','base','ent','fir_name','f','f'),
  ('base','ent','gender','base','ent','gender','f','f'),
  ('base','ent','id','base','ent','id','f','t'),
  ('base','ent','marital','base','ent','marital','f','f'),
  ('base','ent','mid_name','base','ent','mid_name','f','f'),
  ('base','ent','mod_by','base','ent','mod_by','f','f'),
  ('base','ent','mod_date','base','ent','mod_date','f','f'),
  ('base','ent','pref_name','base','ent','pref_name','f','f'),
  ('base','ent','tax_id','base','ent','tax_id','f','f'),
  ('base','ent','title','base','ent','title','f','f'),
  ('base','ent','username','base','ent','username','f','f'),
  ('base','ent_audit','a_action','base','ent_audit','a_action','f','f'),
  ('base','ent_audit','a_by','base','ent_audit','a_by','f','f'),
  ('base','ent_audit','a_date','base','ent_audit','a_date','f','f'),
  ('base','ent_audit','a_seq','base','ent_audit','a_seq','f','t'),
  ('base','ent_audit','a_values','base','ent_audit','a_values','f','f'),
  ('base','ent_audit','id','base','ent_audit','id','f','t'),
  ('base','ent_link','crt_by','base','ent_link','crt_by','f','f'),
  ('base','ent_link','crt_date','base','ent_link','crt_date','f','f'),
  ('base','ent_link','mem','base','ent_link','mem','f','t'),
  ('base','ent_link','mod_by','base','ent_link','mod_by','f','f'),
  ('base','ent_link','mod_date','base','ent_link','mod_date','f','f'),
  ('base','ent_link','org','base','ent_link','org','f','t'),
  ('base','ent_link','role','base','ent_link','role','f','f'),
  ('base','ent_link','supr_path','base','ent_link','supr_path','f','f'),
  ('base','ent_link_v','crt_by','base','ent_link','crt_by','f','f'),
  ('base','ent_link_v','crt_date','base','ent_link','crt_date','f','f'),
  ('base','ent_link_v','mem','base','ent_link','mem','f','t'),
  ('base','ent_link_v','mem_name','base','ent_link_v','mem_name','f','f'),
  ('base','ent_link_v','mod_by','base','ent_link','mod_by','f','f'),
  ('base','ent_link_v','mod_date','base','ent_link','mod_date','f','f'),
  ('base','ent_link_v','org','base','ent_link','org','f','t'),
  ('base','ent_link_v','org_name','base','ent_link_v','org_name','f','f'),
  ('base','ent_link_v','role','base','ent_link','role','f','f'),
  ('base','ent_link_v','supr_path','base','ent_link','supr_path','f','f'),
  ('base','ent_v','age','base','ent_v','age','f','f'),
  ('base','ent_v','bank','base','ent','bank','f','f'),
  ('base','ent_v','born_date','base','ent','born_date','f','f'),
  ('base','ent_v','cas_name','base','ent_v','cas_name','f','f'),
  ('base','ent_v','conn_pub','base','ent','conn_pub','f','f'),
  ('base','ent_v','country','base','ent','country','f','f'),
  ('base','ent_v','crt_by','base','ent','crt_by','f','f'),
  ('base','ent_v','crt_date','base','ent','crt_date','f','f'),
  ('base','ent_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('base','ent_v','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent_v','ent_name','base','ent','ent_name','f','f'),
  ('base','ent_v','ent_num','base','ent','ent_num','f','f'),
  ('base','ent_v','ent_type','base','ent','ent_type','f','f'),
  ('base','ent_v','fir_name','base','ent','fir_name','f','f'),
  ('base','ent_v','frm_name','base','ent_v','frm_name','f','f'),
  ('base','ent_v','gender','base','ent','gender','f','f'),
  ('base','ent_v','giv_name','base','ent_v','giv_name','f','f'),
  ('base','ent_v','id','base','ent','id','f','t'),
  ('base','ent_v','marital','base','ent','marital','f','f'),
  ('base','ent_v','mid_name','base','ent','mid_name','f','f'),
  ('base','ent_v','mod_by','base','ent','mod_by','f','f'),
  ('base','ent_v','mod_date','base','ent','mod_date','f','f'),
  ('base','ent_v','pref_name','base','ent','pref_name','f','f'),
  ('base','ent_v','std_name','base','ent_v','std_name','f','f'),
  ('base','ent_v','tax_id','base','ent','tax_id','f','f'),
  ('base','ent_v','title','base','ent','title','f','f'),
  ('base','ent_v','username','base','ent','username','f','f'),
  ('base','ent_v_pub','crt_by','base','ent','crt_by','f','f'),
  ('base','ent_v_pub','crt_date','base','ent','crt_date','f','f'),
  ('base','ent_v_pub','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent_v_pub','ent_num','base','ent','ent_num','f','f'),
  ('base','ent_v_pub','ent_type','base','ent','ent_type','f','f'),
  ('base','ent_v_pub','id','base','ent','id','f','t'),
  ('base','ent_v_pub','mod_by','base','ent','mod_by','f','f'),
  ('base','ent_v_pub','mod_date','base','ent','mod_date','f','f'),
  ('base','ent_v_pub','std_name','base','ent_v','std_name','f','f'),
  ('base','ent_v_pub','username','base','ent','username','f','f'),
  ('base','file','crt_by','base','file','crt_by','f','f'),
  ('base','file','crt_date','base','file','crt_date','f','f'),
  ('base','file','file_cks','base','file','file_cks','f','f'),
  ('base','file','file_cmt','base','file','file_cmt','f','f'),
  ('base','file','file_data','base','file','file_data','f','f'),
  ('base','file','file_ent','base','file','file_ent','f','t'),
  ('base','file','file_fmt','base','file','file_fmt','f','f'),
  ('base','file','file_prim','base','file','file_prim','f','f'),
  ('base','file','file_priv','base','file','file_priv','f','f'),
  ('base','file','file_seq','base','file','file_seq','f','t'),
  ('base','file','file_type','base','file','file_type','f','f'),
  ('base','file','mod_by','base','file','mod_by','f','f'),
  ('base','file','mod_date','base','file','mod_date','f','f'),
  ('base','file_prim','prim_ent','base','file_prim','prim_ent','f','t'),
  ('base','file_prim','prim_seq','base','file_prim','prim_seq','f','t'),
  ('base','file_prim','prim_type','base','file_prim','prim_type','f','t'),
  ('base','file_v','crt_by','base','file','crt_by','f','f'),
  ('base','file_v','crt_date','base','file','crt_date','f','f'),
  ('base','file_v','file_cks','base','file','file_cks','f','f'),
  ('base','file_v','file_cmt','base','file','file_cmt','f','f'),
  ('base','file_v','file_data','base','file','file_data','f','f'),
  ('base','file_v','file_ent','base','file','file_ent','f','t'),
  ('base','file_v','file_fmt','base','file','file_fmt','f','f'),
  ('base','file_v','file_prim','base','file_v','file_prim','f','f'),
  ('base','file_v','file_priv','base','file','file_priv','f','f'),
  ('base','file_v','file_seq','base','file','file_seq','f','t'),
  ('base','file_v','file_type','base','file','file_type','f','f'),
  ('base','file_v','mod_by','base','file','mod_by','f','f'),
  ('base','file_v','mod_date','base','file','mod_date','f','f'),
  ('base','file_v','std_name','base','ent_v','std_name','f','f'),
  ('base','language','code','base','language','code','f','t'),
  ('base','language','eng_name','base','language','eng_name','f','f'),
  ('base','language','fra_name','base','language','fra_name','f','f'),
  ('base','language','iso_2','base','language','iso_2','f','f'),
  ('base','language','iso_3b','base','language','iso_3b','f','f'),
  ('base','language_v','code','base','language','code','f','t'),
  ('base','language_v','columns','base','language_v','columns','f','f'),
  ('base','language_v','eng_name','base','language','eng_name','f','f'),
  ('base','language_v','fra_name','base','language','fra_name','f','f'),
  ('base','language_v','iso_2','base','language','iso_2','f','f'),
  ('base','language_v','iso_3b','base','language','iso_3b','f','f'),
  ('base','language_v','messages','base','language_v','messages','f','f'),
  ('base','language_v','tables','base','language_v','tables','f','f'),
  ('base','language_v','values','base','language_v','values','f','f'),
  ('base','parm','cmt','base','parm','cmt','f','f'),
  ('base','parm','crt_by','base','parm','crt_by','f','f'),
  ('base','parm','crt_date','base','parm','crt_date','f','f'),
  ('base','parm','mod_by','base','parm','mod_by','f','f'),
  ('base','parm','mod_date','base','parm','mod_date','f','f'),
  ('base','parm','module','base','parm','module','f','t'),
  ('base','parm','parm','base','parm','parm','f','t'),
  ('base','parm','type','base','parm','type','f','f'),
  ('base','parm','v_boolean','base','parm','v_boolean','f','f'),
  ('base','parm','v_date','base','parm','v_date','f','f'),
  ('base','parm','v_float','base','parm','v_float','f','f'),
  ('base','parm','v_int','base','parm','v_int','f','f'),
  ('base','parm','v_text','base','parm','v_text','f','f'),
  ('base','parm_audit','a_action','base','parm_audit','a_action','f','f'),
  ('base','parm_audit','a_by','base','parm_audit','a_by','f','f'),
  ('base','parm_audit','a_date','base','parm_audit','a_date','f','f'),
  ('base','parm_audit','a_seq','base','parm_audit','a_seq','f','t'),
  ('base','parm_audit','a_values','base','parm_audit','a_values','f','f'),
  ('base','parm_audit','module','base','parm_audit','module','f','t'),
  ('base','parm_audit','parm','base','parm_audit','parm','f','t'),
  ('base','parm_v','cmt','base','parm','cmt','f','f'),
  ('base','parm_v','crt_by','base','parm','crt_by','f','f'),
  ('base','parm_v','crt_date','base','parm','crt_date','f','f'),
  ('base','parm_v','mod_by','base','parm','mod_by','f','f'),
  ('base','parm_v','mod_date','base','parm','mod_date','f','f'),
  ('base','parm_v','module','base','parm','module','f','t'),
  ('base','parm_v','parm','base','parm','parm','f','t'),
  ('base','parm_v','type','base','parm','type','f','f'),
  ('base','parm_v','value','base','parm_v','value','f','f'),
  ('base','priv','cmt','base','priv','cmt','f','f'),
  ('base','priv','grantee','base','priv','grantee','f','t'),
  ('base','priv','level','base','priv','level','f','f'),
  ('base','priv','priv','base','priv','priv','f','t'),
  ('base','priv','priv_level','base','priv','priv_level','f','f'),
  ('base','priv_v','cmt','base','priv','cmt','f','f'),
  ('base','priv_v','grantee','base','priv','grantee','f','t'),
  ('base','priv_v','level','base','priv','level','f','f'),
  ('base','priv_v','priv','base','priv','priv','f','t'),
  ('base','priv_v','priv_level','base','priv','priv_level','f','f'),
  ('base','priv_v','priv_list','base','priv_v','priv_list','f','f'),
  ('base','priv_v','std_name','base','ent_v','std_name','f','f'),
  ('base','priv_v','username','base','ent','username','f','f'),
  ('base','token','allows','base','token','allows','f','f'),
  ('base','token','crt_by','base','token','crt_by','f','f'),
  ('base','token','crt_date','base','token','crt_date','f','f'),
  ('base','token','expires','base','token','expires','f','f'),
  ('base','token','mod_by','base','token','mod_by','f','f'),
  ('base','token','mod_date','base','token','mod_date','f','f'),
  ('base','token','token','base','token','token','f','f'),
  ('base','token','token_ent','base','token','token_ent','f','t'),
  ('base','token','token_seq','base','token','token_seq','f','t'),
  ('base','token','used','base','token','used','f','f'),
  ('base','token_v','allows','base','token','allows','f','f'),
  ('base','token_v','crt_by','base','token','crt_by','f','f'),
  ('base','token_v','crt_date','base','token','crt_date','f','f'),
  ('base','token_v','expired','base','token_v','expired','f','f'),
  ('base','token_v','expires','base','token','expires','f','f'),
  ('base','token_v','mod_by','base','token','mod_by','f','f'),
  ('base','token_v','mod_date','base','token','mod_date','f','f'),
  ('base','token_v','std_name','base','ent_v','std_name','f','f'),
  ('base','token_v','token','base','token','token','f','f'),
  ('base','token_v','token_ent','base','token','token_ent','f','t'),
  ('base','token_v','token_seq','base','token','token_seq','f','t'),
  ('base','token_v','used','base','token','used','f','f'),
  ('base','token_v','username','base','ent','username','f','f'),
  ('base','token_v','valid','base','token_v','valid','f','f'),
  ('base','token_v_ticket','allows','base','token','allows','f','f'),
  ('base','token_v_ticket','expires','base','token','expires','f','f'),
  ('base','token_v_ticket','host','base','token_v_ticket','host','f','f'),
  ('base','token_v_ticket','port','base','token_v_ticket','port','f','f'),
  ('base','token_v_ticket','token','base','token','token','f','f'),
  ('base','token_v_ticket','token_ent','base','token','token_ent','f','t'),
  ('json','cert','chad','json','cert','chad','f','f'),
  ('json','cert','connect','json','cert','connect','f','f'),
  ('json','cert','date','json','cert','date','f','f'),
  ('json','cert','file','json','cert','file','f','f'),
  ('json','cert','id','base','ent','id','f','t'),
  ('json','cert','identity','json','cert','identity','f','f'),
  ('json','cert','name','json','cert','name','f','f'),
  ('json','cert','place','json','cert','place','f','f'),
  ('json','cert','public','json','cert','public','f','f'),
  ('json','cert','type','json','place','type','f','f'),
  ('json','connect','address','json','connect','address','f','f'),
  ('json','connect','comment','json','connect','comment','f','f'),
  ('json','connect','id','json','connect','id','f','t'),
  ('json','connect','main','json','connect','main','f','f'),
  ('json','connect','media','json','connect','media','f','f'),
  ('json','connect','prior','json','connect','prior','f','f'),
  ('json','connect','private','json','connect','private','f','f'),
  ('json','connect','seq','json','connect','seq','f','t'),
  ('json','contract','digest','mychips','contracts','digest','f','f'),
  ('json','contract','domain','mychips','contracts','domain','f','t'),
  ('json','contract','language','mychips','contracts','language','f','t'),
  ('json','contract','name','mychips','contracts','name','f','t'),
  ('json','contract','published','mychips','contracts','published','f','f'),
  ('json','contract','sections','mychips','contracts','sections','f','f'),
  ('json','contract','tag','mychips','contracts','tag','f','f'),
  ('json','contract','text','mychips','contracts','text','f','f'),
  ('json','contract','title','mychips','contracts','title','f','f'),
  ('json','contract','version','mychips','contracts','version','f','t'),
  ('json','file','comment','json','file','comment','f','f'),
  ('json','file','data','json','file','data','f','f'),
  ('json','file','digest','json','file','digest','f','f'),
  ('json','file','format','json','file','format','f','f'),
  ('json','file','id','json','file','id','f','t'),
  ('json','file','main','json','file','main','f','f'),
  ('json','file','media','json','file','media','f','f'),
  ('json','file','private','json','file','private','f','f'),
  ('json','file','seq','json','file','seq','f','t'),
  ('json','place','address','json','place','address','f','f'),
  ('json','place','city','base','addr','city','f','f'),
  ('json','place','comment','json','place','comment','f','f'),
  ('json','place','country','base','addr','country','f','f'),
  ('json','place','id','json','place','id','f','t'),
  ('json','place','main','json','place','main','f','f'),
  ('json','place','post','json','place','post','f','f'),
  ('json','place','prior','json','place','prior','f','f'),
  ('json','place','private','json','place','private','f','f'),
  ('json','place','seq','json','place','seq','f','t'),
  ('json','place','state','base','addr','state','f','f'),
  ('json','place','type','json','place','type','f','f'),
  ('json','tally','agree','json','tally','agree','f','f'),
  ('json','tally','comment','mychips','tallies','comment','f','f'),
  ('json','tally','date','json','tally','date','f','f'),
  ('json','tally','holder','json','tally','holder','f','f'),
  ('json','tally','hterms','json','tally','hterms','f','f'),
  ('json','tally','id','json','tally','id','f','t'),
  ('json','tally','partner','json','tally','partner','f','f'),
  ('json','tally','pterms','json','tally','pterms','f','f'),
  ('json','tally','seq','json','tally','seq','f','t'),
  ('json','tally','type','json','tally','type','f','f'),
  ('json','tally','uuid','json','tally','uuid','f','f'),
  ('json','tally','version','mychips','tallies','version','f','f'),
  ('json','user','agent','json','user','agent','f','f'),
  ('json','user','begin','json','user','begin','f','f'),
  ('json','user','cid','json','user','cid','f','f'),
  ('json','user','first','json','user','first','f','f'),
  ('json','user','id','base','ent','id','f','t'),
  ('json','user','juris','json','user','juris','f','f'),
  ('json','user','middle','json','user','middle','f','f'),
  ('json','user','name','json','user','name','f','f'),
  ('json','user','named','json','user','named','f','f'),
  ('json','user','prefer','json','user','prefer','f','f'),
  ('json','user','taxid','json','user','taxid','f','f'),
  ('json','user','type','json','user','type','f','f'),
  ('json','users','agent','json','user','agent','f','f'),
  ('json','users','begin','json','user','begin','f','f'),
  ('json','users','cid','json','user','cid','f','f'),
  ('json','users','connect','json','users','connect','f','f'),
  ('json','users','first','json','user','first','f','f'),
  ('json','users','juris','json','user','juris','f','f'),
  ('json','users','middle','json','user','middle','f','f'),
  ('json','users','name','json','user','name','f','f'),
  ('json','users','place','json','users','place','f','f'),
  ('json','users','prefer','json','user','prefer','f','f'),
  ('json','users','taxid','json','user','taxid','f','f'),
  ('json','users','type','json','user','type','f','f'),
  ('mychips','addr_v_me','addr_cmt','base','addr','addr_cmt','f','f'),
  ('mychips','addr_v_me','addr_ent','base','addr','addr_ent','f','f'),
  ('mychips','addr_v_me','addr_inact','base','addr','addr_inact','f','f'),
  ('mychips','addr_v_me','addr_prim','base','addr_v','addr_prim','f','f'),
  ('mychips','addr_v_me','addr_priv','base','addr','addr_priv','f','f'),
  ('mychips','addr_v_me','addr_seq','base','addr','addr_seq','f','f'),
  ('mychips','addr_v_me','addr_spec','base','addr','addr_spec','f','f'),
  ('mychips','addr_v_me','addr_type','base','addr','addr_type','f','f'),
  ('mychips','addr_v_me','city','base','addr','city','f','f'),
  ('mychips','addr_v_me','country','base','addr','country','f','f'),
  ('mychips','addr_v_me','crt_by','base','addr','crt_by','f','f'),
  ('mychips','addr_v_me','crt_date','base','addr','crt_date','f','f'),
  ('mychips','addr_v_me','mod_by','base','addr','mod_by','f','f'),
  ('mychips','addr_v_me','mod_date','base','addr','mod_date','f','f'),
  ('mychips','addr_v_me','pcode','base','addr','pcode','f','f'),
  ('mychips','addr_v_me','state','base','addr','state','f','f'),
  ('mychips','addr_v_me','std_name','base','ent_v','std_name','f','f'),
  ('mychips','agents','agent','mychips','agents','agent','f','t'),
  ('mychips','agents','agent_host','mychips','agents','agent_host','f','f'),
  ('mychips','agents','agent_ip','mychips','agents','agent_ip','f','f'),
  ('mychips','agents','agent_key','mychips','agents','agent_key','f','f'),
  ('mychips','agents','agent_port','mychips','agents','agent_port','f','f'),
  ('mychips','agents','crt_by','mychips','agents','crt_by','f','f'),
  ('mychips','agents','crt_date','mychips','agents','crt_date','f','f'),
  ('mychips','agents','mod_by','mychips','agents','mod_by','f','f'),
  ('mychips','agents','mod_date','mychips','agents','mod_date','f','f'),
  ('mychips','agents_v','agent','mychips','agents','agent','f','t'),
  ('mychips','agents_v','agent_host','mychips','agents','agent_host','f','f'),
  ('mychips','agents_v','agent_ip','mychips','agents','agent_ip','f','f'),
  ('mychips','agents_v','agent_key','mychips','agents','agent_key','f','f'),
  ('mychips','agents_v','agent_port','mychips','agents','agent_port','f','f'),
  ('mychips','agents_v','atsock','mychips','agents_v','atsock','f','f'),
  ('mychips','agents_v','json','mychips','agents_v','json','f','f'),
  ('mychips','agents_v','sock','mychips','agents_v','sock','f','f'),
  ('mychips','agents_v','valid','mychips','agents_v','valid','f','f'),
  ('mychips','chit_tries','ctry_ent','mychips','chit_tries','ctry_ent','f','t'),
  ('mychips','chit_tries','ctry_idx','mychips','chit_tries','ctry_idx','f','t'),
  ('mychips','chit_tries','ctry_seq','mychips','chit_tries','ctry_seq','f','t'),
  ('mychips','chit_tries','last','mychips','chit_tries','last','f','f'),
  ('mychips','chit_tries','tries','mychips','chit_tries','tries','f','f'),
  ('mychips','chits','chain_hash','mychips','chits','chain_hash','f','f'),
  ('mychips','chits','chain_idx','mychips','chits','chain_idx','f','f'),
  ('mychips','chits','chain_prev','mychips','chits','chain_prev','f','f'),
  ('mychips','chits','chain_send','mychips','chits','chain_send','f','f'),
  ('mychips','chits','chit_date','mychips','chits','chit_date','f','f'),
  ('mychips','chits','chit_ent','mychips','chits','chit_ent','f','t'),
  ('mychips','chits','chit_idx','mychips','chits','chit_idx','f','t'),
  ('mychips','chits','chit_seq','mychips','chits','chit_seq','f','t'),
  ('mychips','chits','chit_type','mychips','chits','chit_type','f','f'),
  ('mychips','chits','chit_uuid','mychips','chits','chit_uuid','f','f'),
  ('mychips','chits','crt_by','mychips','chits','crt_by','f','f'),
  ('mychips','chits','crt_date','mychips','chits','crt_date','f','f'),
  ('mychips','chits','digest','mychips','chits','digest','f','f'),
  ('mychips','chits','issuer','mychips','chits','issuer','f','f'),
  ('mychips','chits','lift_seq','mychips','chits','lift_seq','f','f'),
  ('mychips','chits','memo','mychips','chits','memo','f','f'),
  ('mychips','chits','mod_by','mychips','chits','mod_by','f','f'),
  ('mychips','chits','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','chits','reference','mychips','chits','reference','f','f'),
  ('mychips','chits','request','mychips','chits','request','f','f'),
  ('mychips','chits','signature','mychips','chits','signature','f','f'),
  ('mychips','chits','status','mychips','chits','status','f','f'),
  ('mychips','chits','units','mychips','chits','units','f','f'),
  ('mychips','chits_v','action','mychips','chits_v','action','f','f'),
  ('mychips','chits_v','chain_conf','mychips','tallies','chain_conf','f','f'),
  ('mychips','chits_v','chain_hash','mychips','chits','chain_hash','f','f'),
  ('mychips','chits_v','chain_idx','mychips','chits','chain_idx','f','f'),
  ('mychips','chits_v','chain_prev','mychips','chits','chain_prev','f','f'),
  ('mychips','chits_v','chain_send','mychips','chits','chain_send','f','f'),
  ('mychips','chits_v','chit_date','mychips','chits','chit_date','f','f'),
  ('mychips','chits_v','chit_ent','mychips','chits','chit_ent','f','t'),
  ('mychips','chits_v','chit_idx','mychips','chits','chit_idx','f','t'),
  ('mychips','chits_v','chit_seq','mychips','chits','chit_seq','f','t'),
  ('mychips','chits_v','chit_type','mychips','chits','chit_type','f','f'),
  ('mychips','chits_v','chit_uuid','mychips','chits','chit_uuid','f','f'),
  ('mychips','chits_v','clean','mychips','chits_v','clean','f','f'),
  ('mychips','chits_v','crt_by','mychips','chits','crt_by','f','f'),
  ('mychips','chits_v','crt_date','mychips','chits','crt_date','f','f'),
  ('mychips','chits_v','cstate','mychips','chits_v','cstate','f','f'),
  ('mychips','chits_v','digest','mychips','chits','digest','f','f'),
  ('mychips','chits_v','hash_v','mychips','chits_v','hash_v','f','f'),
  ('mychips','chits_v','hold_cid','mychips','tallies','hold_cid','f','f'),
  ('mychips','chits_v','issuer','mychips','chits','issuer','f','f'),
  ('mychips','chits_v','json','mychips','chits_v','json','f','f'),
  ('mychips','chits_v','json_core','mychips','chits_v','json_core','f','f'),
  ('mychips','chits_v','lift_seq','mychips','chits','lift_seq','f','f'),
  ('mychips','chits_v','memo','mychips','chits','memo','f','f'),
  ('mychips','chits_v','mod_by','mychips','chits','mod_by','f','f'),
  ('mychips','chits_v','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','chits_v','net','mychips','chits_v','net','f','f'),
  ('mychips','chits_v','net_g','mychips','chits_v','net_g','f','f'),
  ('mychips','chits_v','net_p','mychips','chits_v','net_p','f','f'),
  ('mychips','chits_v','part_cid','mychips','tallies','part_cid','f','f'),
  ('mychips','chits_v','reference','mychips','chits','reference','f','f'),
  ('mychips','chits_v','request','mychips','chits','request','f','f'),
  ('mychips','chits_v','signature','mychips','chits','signature','f','f'),
  ('mychips','chits_v','state','mychips','chits_v','state','f','f'),
  ('mychips','chits_v','status','mychips','chits','status','f','f'),
  ('mychips','chits_v','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','chits_v','tally_uuid','mychips','tallies','tally_uuid','f','f'),
  ('mychips','chits_v','units','mychips','chits','units','f','f'),
  ('mychips','chits_v_chains','chain_conf','mychips','tallies','chain_conf','f','f'),
  ('mychips','chits_v_chains','chain_hash','mychips','chits','chain_hash','f','f'),
  ('mychips','chits_v_chains','chain_idx','mychips','chits','chain_idx','f','f'),
  ('mychips','chits_v_chains','chain_prev','mychips','chits','chain_prev','f','f'),
  ('mychips','chits_v_chains','ent','mychips','chits_v_chains','ent','f','f'),
  ('mychips','chits_v_chains','hash_ok','mychips','chits_v_chains','hash_ok','f','f'),
  ('mychips','chits_v_chains','last','mychips','chits_v_chains','last','f','f'),
  ('mychips','chits_v_chains','length','mychips','chits_v_chains','length','f','f'),
  ('mychips','chits_v_chains','ok','mychips','chits_v_chains','ok','f','f'),
  ('mychips','chits_v_chains','prev_ok','mychips','chits_v_chains','prev_ok','f','f'),
  ('mychips','chits_v_chains','seq','mychips','chits_v_chains','seq','f','f'),
  ('mychips','chits_v_chains','uuids','mychips','chits_v_chains','uuids','f','f'),
  ('mychips','chits_v_me','action','mychips','chits_v','action','f','f'),
  ('mychips','chits_v_me','chain_conf','mychips','tallies','chain_conf','f','f'),
  ('mychips','chits_v_me','chain_hash','mychips','chits','chain_hash','f','f'),
  ('mychips','chits_v_me','chain_idx','mychips','chits','chain_idx','f','f'),
  ('mychips','chits_v_me','chain_prev','mychips','chits','chain_prev','f','f'),
  ('mychips','chits_v_me','chain_send','mychips','chits','chain_send','f','f'),
  ('mychips','chits_v_me','chit_date','mychips','chits','chit_date','f','f'),
  ('mychips','chits_v_me','chit_ent','mychips','chits','chit_ent','f','t'),
  ('mychips','chits_v_me','chit_idx','mychips','chits','chit_idx','f','t'),
  ('mychips','chits_v_me','chit_seq','mychips','chits','chit_seq','f','t'),
  ('mychips','chits_v_me','chit_type','mychips','chits','chit_type','f','f'),
  ('mychips','chits_v_me','chit_uuid','mychips','chits','chit_uuid','f','f'),
  ('mychips','chits_v_me','clean','mychips','chits_v','clean','f','f'),
  ('mychips','chits_v_me','crt_by','mychips','chits','crt_by','f','f'),
  ('mychips','chits_v_me','crt_date','mychips','chits','crt_date','f','f'),
  ('mychips','chits_v_me','cstate','mychips','chits_v','cstate','f','f'),
  ('mychips','chits_v_me','digest','mychips','chits','digest','f','f'),
  ('mychips','chits_v_me','hash_v','mychips','chits_v','hash_v','f','f'),
  ('mychips','chits_v_me','hold_cid','mychips','tallies','hold_cid','f','f'),
  ('mychips','chits_v_me','issuer','mychips','chits','issuer','f','f'),
  ('mychips','chits_v_me','json','mychips','chits_v','json','f','f'),
  ('mychips','chits_v_me','json_core','mychips','chits_v','json_core','f','f'),
  ('mychips','chits_v_me','lift_seq','mychips','chits','lift_seq','f','f'),
  ('mychips','chits_v_me','memo','mychips','chits','memo','f','f'),
  ('mychips','chits_v_me','mod_by','mychips','chits','mod_by','f','f'),
  ('mychips','chits_v_me','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','chits_v_me','net','mychips','chits_v','net','f','f'),
  ('mychips','chits_v_me','net_g','mychips','chits_v','net_g','f','f'),
  ('mychips','chits_v_me','net_p','mychips','chits_v','net_p','f','f'),
  ('mychips','chits_v_me','part_cid','mychips','tallies','part_cid','f','f'),
  ('mychips','chits_v_me','reference','mychips','chits','reference','f','f'),
  ('mychips','chits_v_me','request','mychips','chits','request','f','f'),
  ('mychips','chits_v_me','signature','mychips','chits','signature','f','f'),
  ('mychips','chits_v_me','state','mychips','chits_v','state','f','f'),
  ('mychips','chits_v_me','status','mychips','chits','status','f','f'),
  ('mychips','chits_v_me','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','chits_v_me','tally_uuid','mychips','tallies','tally_uuid','f','f'),
  ('mychips','chits_v_me','units','mychips','chits','units','f','f'),
  ('mychips','comm_v_me','comm_cmt','base','comm','comm_cmt','f','f'),
  ('mychips','comm_v_me','comm_ent','base','comm','comm_ent','f','f'),
  ('mychips','comm_v_me','comm_inact','base','comm','comm_inact','f','f'),
  ('mychips','comm_v_me','comm_prim','base','comm_v','comm_prim','f','f'),
  ('mychips','comm_v_me','comm_priv','base','comm','comm_priv','f','f'),
  ('mychips','comm_v_me','comm_seq','base','comm','comm_seq','f','f'),
  ('mychips','comm_v_me','comm_spec','base','comm','comm_spec','f','f'),
  ('mychips','comm_v_me','comm_type','base','comm','comm_type','f','f'),
  ('mychips','comm_v_me','crt_by','base','comm','crt_by','f','f'),
  ('mychips','comm_v_me','crt_date','base','comm','crt_date','f','f'),
  ('mychips','comm_v_me','mod_by','base','comm','mod_by','f','f'),
  ('mychips','comm_v_me','mod_date','base','comm','mod_date','f','f'),
  ('mychips','comm_v_me','std_name','base','ent_v','std_name','f','f'),
  ('mychips','contracts','crt_by','mychips','contracts','crt_by','f','f'),
  ('mychips','contracts','crt_date','mychips','contracts','crt_date','f','f'),
  ('mychips','contracts','digest','mychips','contracts','digest','f','f'),
  ('mychips','contracts','domain','mychips','contracts','domain','f','t'),
  ('mychips','contracts','language','mychips','contracts','language','f','t'),
  ('mychips','contracts','mod_by','mychips','contracts','mod_by','f','f'),
  ('mychips','contracts','mod_date','mychips','contracts','mod_date','f','f'),
  ('mychips','contracts','name','mychips','contracts','name','f','t'),
  ('mychips','contracts','published','mychips','contracts','published','f','f'),
  ('mychips','contracts','sections','mychips','contracts','sections','f','f'),
  ('mychips','contracts','tag','mychips','contracts','tag','f','f'),
  ('mychips','contracts','text','mychips','contracts','text','f','f'),
  ('mychips','contracts','title','mychips','contracts','title','f','f'),
  ('mychips','contracts','version','mychips','contracts','version','f','t'),
  ('mychips','contracts_v','clean','mychips','contracts_v','clean','f','f'),
  ('mychips','contracts_v','crt_by','mychips','contracts','crt_by','f','f'),
  ('mychips','contracts_v','crt_date','mychips','contracts','crt_date','f','f'),
  ('mychips','contracts_v','digest','mychips','contracts','digest','f','f'),
  ('mychips','contracts_v','digest_v','mychips','contracts_v','digest_v','f','f'),
  ('mychips','contracts_v','domain','mychips','contracts','domain','f','t'),
  ('mychips','contracts_v','json','mychips','contracts_v','json','f','f'),
  ('mychips','contracts_v','json_core','mychips','contracts_v','json_core','f','f'),
  ('mychips','contracts_v','language','mychips','contracts','language','f','t'),
  ('mychips','contracts_v','mod_by','mychips','contracts','mod_by','f','f'),
  ('mychips','contracts_v','mod_date','mychips','contracts','mod_date','f','f'),
  ('mychips','contracts_v','name','mychips','contracts','name','f','t'),
  ('mychips','contracts_v','published','mychips','contracts','published','f','f'),
  ('mychips','contracts_v','sections','mychips','contracts','sections','f','f'),
  ('mychips','contracts_v','source','mychips','contracts_v','source','f','f'),
  ('mychips','contracts_v','tag','mychips','contracts','tag','f','f'),
  ('mychips','contracts_v','text','mychips','contracts','text','f','f'),
  ('mychips','contracts_v','title','mychips','contracts','title','f','f'),
  ('mychips','contracts_v','version','mychips','contracts','version','f','t'),
  ('mychips','file_v_me','crt_by','base','file','crt_by','f','f'),
  ('mychips','file_v_me','crt_date','base','file','crt_date','f','f'),
  ('mychips','file_v_me','file_cks','base','file','file_cks','f','f'),
  ('mychips','file_v_me','file_cmt','base','file','file_cmt','f','f'),
  ('mychips','file_v_me','file_data','base','file','file_data','f','f'),
  ('mychips','file_v_me','file_ent','base','file','file_ent','f','f'),
  ('mychips','file_v_me','file_fmt','base','file','file_fmt','f','f'),
  ('mychips','file_v_me','file_prim','base','file_v','file_prim','f','f'),
  ('mychips','file_v_me','file_priv','base','file','file_priv','f','f'),
  ('mychips','file_v_me','file_seq','base','file','file_seq','f','f'),
  ('mychips','file_v_me','file_type','base','file','file_type','f','f'),
  ('mychips','file_v_me','mod_by','base','file','mod_by','f','f'),
  ('mychips','file_v_me','mod_date','base','file','mod_date','f','f'),
  ('mychips','file_v_me','std_name','base','ent_v','std_name','f','f'),
  ('mychips','lifts','circuit','mychips','lifts','circuit','f','f'),
  ('mychips','lifts','crt_by','mychips','lifts','crt_by','f','f'),
  ('mychips','lifts','crt_date','mychips','lifts','crt_date','f','f'),
  ('mychips','lifts','digest','mychips','lifts','digest','f','f'),
  ('mychips','lifts','find','mychips','lifts','find','f','f'),
  ('mychips','lifts','life','mychips','lifts','life','f','f'),
  ('mychips','lifts','lift_date','mychips','lifts','lift_date','f','f'),
  ('mychips','lifts','lift_seq','mychips','lifts','lift_seq','f','t'),
  ('mychips','lifts','lift_type','mychips','lifts','lift_type','f','f'),
  ('mychips','lifts','lift_uuid','mychips','lifts','lift_uuid','f','t'),
  ('mychips','lifts','mod_by','mychips','lifts','mod_by','f','f'),
  ('mychips','lifts','mod_date','mychips','lifts','mod_date','f','f'),
  ('mychips','lifts','origin','mychips','lifts','origin','f','f'),
  ('mychips','lifts','referee','mychips','lifts','referee','f','f'),
  ('mychips','lifts','request','mychips','lifts','request','f','f'),
  ('mychips','lifts','signature','mychips','lifts','signature','f','f'),
  ('mychips','lifts','status','mychips','lifts','status','f','f'),
  ('mychips','lifts','tallies','mychips','lifts','tallies','f','f'),
  ('mychips','lifts','units','mychips','lifts','units','f','f'),
  ('mychips','lifts_v','circuit','mychips','lifts','circuit','f','f'),
  ('mychips','lifts_v','clean','mychips','lifts_v','clean','f','f'),
  ('mychips','lifts_v','digest','mychips','lifts','digest','f','f'),
  ('mychips','lifts_v','digest_v','mychips','lifts_v','digest_v','f','f'),
  ('mychips','lifts_v','expires','mychips','lifts_v','expires','f','f'),
  ('mychips','lifts_v','find','mychips','lifts','find','f','f'),
  ('mychips','lifts_v','json','mychips','lifts_v','json','f','f'),
  ('mychips','lifts_v','json_core','mychips','lifts_v','json_core','f','f'),
  ('mychips','lifts_v','life','mychips','lifts','life','f','f'),
  ('mychips','lifts_v','lift_date','mychips','lifts','lift_date','f','f'),
  ('mychips','lifts_v','lift_seq','mychips','lifts','lift_seq','f','t'),
  ('mychips','lifts_v','lift_type','mychips','lifts','lift_type','f','f'),
  ('mychips','lifts_v','lift_uuid','mychips','lifts','lift_uuid','f','t'),
  ('mychips','lifts_v','origin','mychips','lifts','origin','f','f'),
  ('mychips','lifts_v','referee','mychips','lifts','referee','f','f'),
  ('mychips','lifts_v','remains','mychips','lifts_v','remains','f','f'),
  ('mychips','lifts_v','request','mychips','lifts','request','f','f'),
  ('mychips','lifts_v','signature','mychips','lifts','signature','f','f'),
  ('mychips','lifts_v','state','mychips','lifts_v','state','f','f'),
  ('mychips','lifts_v','status','mychips','lifts','status','f','f'),
  ('mychips','lifts_v','tallies','mychips','lifts','tallies','f','f'),
  ('mychips','lifts_v','units','mychips','lifts','units','f','f'),
  ('mychips','lifts_v_dist','bot_chad','mychips','lifts_v_dist','bot_chad','f','f'),
  ('mychips','lifts_v_dist','bot_tally','mychips','lifts_v_dist','bot_tally','f','f'),
  ('mychips','lifts_v_dist','circuit','mychips','lifts','circuit','f','f'),
  ('mychips','lifts_v_dist','clean','mychips','lifts_v','clean','f','f'),
  ('mychips','lifts_v_dist','digest','mychips','lifts','digest','f','f'),
  ('mychips','lifts_v_dist','digest_v','mychips','lifts_v','digest_v','f','f'),
  ('mychips','lifts_v_dist','expires','mychips','lifts_v','expires','f','f'),
  ('mychips','lifts_v_dist','find','mychips','lifts','find','f','f'),
  ('mychips','lifts_v_dist','find_v','mychips','lifts_v_dist','find_v','f','f'),
  ('mychips','lifts_v_dist','inp_chad','mychips','lifts_v_dist','inp_chad','f','f'),
  ('mychips','lifts_v_dist','json','mychips','lifts_v','json','f','f'),
  ('mychips','lifts_v_dist','json_core','mychips','lifts_v','json_core','f','f'),
  ('mychips','lifts_v_dist','life','mychips','lifts','life','f','f'),
  ('mychips','lifts_v_dist','lift_date','mychips','lifts','lift_date','f','f'),
  ('mychips','lifts_v_dist','lift_seq','mychips','lifts','lift_seq','f','t'),
  ('mychips','lifts_v_dist','lift_type','mychips','lifts','lift_type','f','f'),
  ('mychips','lifts_v_dist','lift_uuid','mychips','lifts','lift_uuid','f','t'),
  ('mychips','lifts_v_dist','origin','mychips','lifts','origin','f','f'),
  ('mychips','lifts_v_dist','origin_v','mychips','lifts_v_dist','origin_v','f','f'),
  ('mychips','lifts_v_dist','out_chad','mychips','lifts_v_dist','out_chad','f','f'),
  ('mychips','lifts_v_dist','referee','mychips','lifts','referee','f','f'),
  ('mychips','lifts_v_dist','referee_v','mychips','lifts_v_dist','referee_v','f','f'),
  ('mychips','lifts_v_dist','remains','mychips','lifts_v','remains','f','f'),
  ('mychips','lifts_v_dist','request','mychips','lifts','request','f','f'),
  ('mychips','lifts_v_dist','signature','mychips','lifts','signature','f','f'),
  ('mychips','lifts_v_dist','state','mychips','lifts_v','state','f','f'),
  ('mychips','lifts_v_dist','status','mychips','lifts','status','f','f'),
  ('mychips','lifts_v_dist','tallies','mychips','lifts','tallies','f','f'),
  ('mychips','lifts_v_dist','top_chad','mychips','lifts_v_dist','top_chad','f','f'),
  ('mychips','lifts_v_dist','top_tally','mychips','lifts_v_dist','top_tally','f','f'),
  ('mychips','lifts_v_dist','units','mychips','lifts','units','f','f'),
  ('mychips','route_tries','last','mychips','route_tries','last','f','f'),
  ('mychips','route_tries','rtry_rid','mychips','route_tries','rtry_rid','f','t'),
  ('mychips','route_tries','tries','mychips','route_tries','tries','f','f'),
  ('mychips','routes','dst_agent','mychips','routes','dst_agent','f','f'),
  ('mychips','routes','dst_cid','mychips','routes','dst_cid','f','f'),
  ('mychips','routes','good_date','mychips','routes','good_date','f','f'),
  ('mychips','routes','lift_count','mychips','routes','lift_count','f','f'),
  ('mychips','routes','lift_date','mychips','routes','lift_date','f','f'),
  ('mychips','routes','margin','mychips','routes','margin','f','f'),
  ('mychips','routes','max','mychips','routes','max','f','f'),
  ('mychips','routes','min','mychips','routes','min','f','f'),
  ('mychips','routes','req_ent','mychips','routes','req_ent','f','f'),
  ('mychips','routes','req_tseq','mychips','routes','req_tseq','f','f'),
  ('mychips','routes','reward','mychips','routes','reward','f','f'),
  ('mychips','routes','rid','mychips','routes','rid','f','t'),
  ('mychips','routes','status','mychips','routes','status','f','f'),
  ('mychips','routes','step','mychips','routes','step','f','f'),
  ('mychips','routes','via_ent','mychips','routes','via_ent','f','f'),
  ('mychips','routes','via_tseq','mychips','routes','via_tseq','f','f'),
  ('mychips','routes_v','dst_agent','mychips','routes','dst_agent','f','f'),
  ('mychips','routes_v','dst_chad','mychips','routes_v','dst_chad','f','f'),
  ('mychips','routes_v','dst_cid','mychips','routes','dst_cid','f','f'),
  ('mychips','routes_v','expired','mychips','routes_v','expired','f','f'),
  ('mychips','routes_v','expires','mychips','routes_v','expires','f','f'),
  ('mychips','routes_v','good_date','mychips','routes','good_date','f','f'),
  ('mychips','routes_v','json','mychips','routes_v','json','f','f'),
  ('mychips','routes_v','lading','mychips','routes_v','lading','f','f'),
  ('mychips','routes_v','last','mychips','route_tries','last','f','f'),
  ('mychips','routes_v','lift_count','mychips','routes','lift_count','f','f'),
  ('mychips','routes_v','lift_date','mychips','routes','lift_date','f','f'),
  ('mychips','routes_v','margin','mychips','routes','margin','f','f'),
  ('mychips','routes_v','max','mychips','routes','max','f','f'),
  ('mychips','routes_v','min','mychips','routes','min','f','f'),
  ('mychips','routes_v','native','mychips','routes_v','native','f','f'),
  ('mychips','routes_v','req_agent','mychips','routes_v','req_agent','f','f'),
  ('mychips','routes_v','req_chad','mychips','routes_v','req_chad','f','f'),
  ('mychips','routes_v','req_cid','mychips','routes_v','req_cid','f','f'),
  ('mychips','routes_v','req_ent','mychips','routes','req_ent','f','f'),
  ('mychips','routes_v','req_tally','mychips','routes_v','req_tally','f','f'),
  ('mychips','routes_v','req_tseq','mychips','routes','req_tseq','f','f'),
  ('mychips','routes_v','reward','mychips','routes','reward','f','f'),
  ('mychips','routes_v','rid','mychips','routes','rid','f','t'),
  ('mychips','routes_v','rpt_agent','mychips','routes_v','rpt_agent','f','f'),
  ('mychips','routes_v','rpt_chad','mychips','routes_v','rpt_chad','f','f'),
  ('mychips','routes_v','rpt_cid','mychips','routes_v','rpt_cid','f','f'),
  ('mychips','routes_v','state','mychips','routes_v','state','f','f'),
  ('mychips','routes_v','status','mychips','routes','status','f','f'),
  ('mychips','routes_v','step','mychips','routes','step','f','f'),
  ('mychips','routes_v','tries','mychips','route_tries','tries','f','f'),
  ('mychips','routes_v','via_agent','mychips','routes_v','via_agent','f','f'),
  ('mychips','routes_v','via_chad','mychips','routes_v','via_chad','f','f'),
  ('mychips','routes_v','via_cid','mychips','routes_v','via_cid','f','f'),
  ('mychips','routes_v','via_ent','mychips','routes','via_ent','f','f'),
  ('mychips','routes_v','via_tally','mychips','routes_v','via_tally','f','f'),
  ('mychips','routes_v','via_tseq','mychips','routes','via_tseq','f','f'),
  ('mychips','routes_v','vip_agent','mychips','routes_v','vip_agent','f','f'),
  ('mychips','routes_v','vip_chad','mychips','routes_v','vip_chad','f','f'),
  ('mychips','routes_v','vip_cid','mychips','routes_v','vip_cid','f','f'),
  ('mychips','routes_v_paths','at','mychips','tallies_v_paths','at','f','f'),
  ('mychips','routes_v_paths','ath','mychips','tallies_v_paths','ath','f','f'),
  ('mychips','routes_v_paths','bang','mychips','tallies_v_paths','bang','f','f'),
  ('mychips','routes_v_paths','bot','mychips','tallies_v_paths','bot','f','f'),
  ('mychips','routes_v_paths','bot_agent','mychips','tallies_v_paths','bot_agent','f','f'),
  ('mychips','routes_v_paths','bot_chad','mychips','tallies_v_paths','bot_chad','f','f'),
  ('mychips','routes_v_paths','bot_cid','mychips','tallies_v_paths','bot_cid','f','f'),
  ('mychips','routes_v_paths','bot_tseq','mychips','tallies_v_paths','bot_tseq','f','f'),
  ('mychips','routes_v_paths','bot_uuid','mychips','tallies_v_paths','bot_uuid','f','f'),
  ('mychips','routes_v_paths','circuit','mychips','routes_v_paths','circuit','f','f'),
  ('mychips','routes_v_paths','dst_agent','mychips','routes','dst_agent','f','f'),
  ('mychips','routes_v_paths','dst_cid','mychips','routes','dst_cid','f','f'),
  ('mychips','routes_v_paths','edges','mychips','tallies_v_paths','edges','f','f'),
  ('mychips','routes_v_paths','ents','mychips','tallies_v_paths','ents','f','f'),
  ('mychips','routes_v_paths','fori','mychips','tallies_v_paths','fori','f','f'),
  ('mychips','routes_v_paths','foro','mychips','tallies_v_paths','foro','f','f'),
  ('mychips','routes_v_paths','inp','mychips','tallies_v_net','inp','f','f'),
  ('mychips','routes_v_paths','inp_agent','mychips','tallies_v_paths','inp_agent','f','f'),
  ('mychips','routes_v_paths','inp_chad','mychips','tallies_v_paths','inp_chad','f','f'),
  ('mychips','routes_v_paths','inp_cid','mychips','tallies_v_paths','inp_cid','f','f'),
  ('mychips','routes_v_paths','lift_count','mychips','routes','lift_count','f','f'),
  ('mychips','routes_v_paths','margin','mychips','tallies_v_net','margin','f','f'),
  ('mychips','routes_v_paths','max','mychips','tallies_v_net','max','f','f'),
  ('mychips','routes_v_paths','min','mychips','tallies_v_net','min','f','f'),
  ('mychips','routes_v_paths','native','mychips','routes_v','native','f','f'),
  ('mychips','routes_v_paths','nodes','mychips','tallies_v_paths','nodes','f','f'),
  ('mychips','routes_v_paths','out','mychips','tallies_v_net','out','f','f'),
  ('mychips','routes_v_paths','out_agent','mychips','tallies_v_paths','out_agent','f','f'),
  ('mychips','routes_v_paths','out_chad','mychips','tallies_v_paths','out_chad','f','f'),
  ('mychips','routes_v_paths','out_cid','mychips','tallies_v_paths','out_cid','f','f'),
  ('mychips','routes_v_paths','pat','mychips','tallies_v_paths','pat','f','f'),
  ('mychips','routes_v_paths','path','mychips','tallies_v_paths','path','f','f'),
  ('mychips','routes_v_paths','path_margin','mychips','routes_v_paths','path_margin','f','f'),
  ('mychips','routes_v_paths','path_max','mychips','routes_v_paths','path_max','f','f'),
  ('mychips','routes_v_paths','path_min','mychips','routes_v_paths','path_min','f','f'),
  ('mychips','routes_v_paths','path_reward','mychips','routes_v_paths','path_reward','f','f'),
  ('mychips','routes_v_paths','req_agent','mychips','routes_v','req_agent','f','f'),
  ('mychips','routes_v_paths','req_chad','mychips','routes_v','req_chad','f','f'),
  ('mychips','routes_v_paths','req_cid','mychips','routes_v','req_cid','f','f'),
  ('mychips','routes_v_paths','req_ent','mychips','routes','req_ent','f','f'),
  ('mychips','routes_v_paths','req_tally','mychips','routes_v','req_tally','f','f'),
  ('mychips','routes_v_paths','req_tseq','mychips','routes','req_tseq','f','f'),
  ('mychips','routes_v_paths','reward','mychips','tallies','reward','f','f'),
  ('mychips','routes_v_paths','rid','mychips','routes','rid','f','t'),
  ('mychips','routes_v_paths','route_margin','mychips','routes_v_paths','route_margin','f','f'),
  ('mychips','routes_v_paths','route_max','mychips','routes_v_paths','route_max','f','f'),
  ('mychips','routes_v_paths','route_min','mychips','routes_v_paths','route_min','f','f'),
  ('mychips','routes_v_paths','route_reward','mychips','routes_v_paths','route_reward','f','f'),
  ('mychips','routes_v_paths','rpt_agent','mychips','routes_v','rpt_agent','f','f'),
  ('mychips','routes_v_paths','rpt_chad','mychips','routes_v','rpt_chad','f','f'),
  ('mychips','routes_v_paths','rpt_cid','mychips','routes_v','rpt_cid','f','f'),
  ('mychips','routes_v_paths','segment','mychips','tallies_v_paths','segment','f','f'),
  ('mychips','routes_v_paths','seqs','mychips','tallies_v_paths','seqs','f','f'),
  ('mychips','routes_v_paths','status','mychips','routes','status','f','f'),
  ('mychips','routes_v_paths','top','mychips','tallies_v_paths','top','f','f'),
  ('mychips','routes_v_paths','top_agent','mychips','tallies_v_paths','top_agent','f','f'),
  ('mychips','routes_v_paths','top_chad','mychips','tallies_v_paths','top_chad','f','f'),
  ('mychips','routes_v_paths','top_cid','mychips','tallies_v_paths','top_cid','f','f'),
  ('mychips','routes_v_paths','top_tseq','mychips','tallies_v_paths','top_tseq','f','f'),
  ('mychips','routes_v_paths','top_uuid','mychips','tallies_v_paths','top_uuid','f','f'),
  ('mychips','routes_v_paths','uuids','mychips','tallies_v_paths','uuids','f','f'),
  ('mychips','routes_v_paths','via_ent','mychips','routes','via_ent','f','f'),
  ('mychips','routes_v_paths','via_tally','mychips','routes_v','via_tally','f','f'),
  ('mychips','routes_v_paths','via_tseq','mychips','routes','via_tseq','f','f'),
  ('mychips','routes_v_query','at','mychips','tallies_v_paths','at','f','f'),
  ('mychips','routes_v_query','ath','mychips','tallies_v_paths','ath','f','f'),
  ('mychips','routes_v_query','bang','mychips','tallies_v_paths','bang','f','f'),
  ('mychips','routes_v_query','bot','mychips','tallies_v_paths','bot','f','f'),
  ('mychips','routes_v_query','bot_agent','mychips','tallies_v_paths','bot_agent','f','f'),
  ('mychips','routes_v_query','bot_chad','mychips','tallies_v_paths','bot_chad','f','f'),
  ('mychips','routes_v_query','bot_cid','mychips','tallies_v_paths','bot_cid','f','f'),
  ('mychips','routes_v_query','bot_tseq','mychips','tallies_v_paths','bot_tseq','f','f'),
  ('mychips','routes_v_query','bot_uuid','mychips','tallies_v_paths','bot_uuid','f','f'),
  ('mychips','routes_v_query','circuit','mychips','tallies_v_paths','circuit','f','f'),
  ('mychips','routes_v_query','dst_agent','mychips','routes','dst_agent','f','f'),
  ('mychips','routes_v_query','dst_cid','mychips','routes','dst_cid','f','f'),
  ('mychips','routes_v_query','edges','mychips','tallies_v_paths','edges','f','f'),
  ('mychips','routes_v_query','ents','mychips','tallies_v_paths','ents','f','f'),
  ('mychips','routes_v_query','exist','mychips','routes_v_query','exist','f','f'),
  ('mychips','routes_v_query','expired','mychips','routes_v','expired','f','f'),
  ('mychips','routes_v_query','find_agent','mychips','routes_v_query','find_agent','f','f'),
  ('mychips','routes_v_query','find_cid','mychips','routes_v_query','find_cid','f','f'),
  ('mychips','routes_v_query','fori','mychips','tallies_v_paths','fori','f','f'),
  ('mychips','routes_v_query','foro','mychips','tallies_v_paths','foro','f','f'),
  ('mychips','routes_v_query','inp','mychips','tallies_v_net','inp','f','f'),
  ('mychips','routes_v_query','inp_agent','mychips','tallies_v_paths','inp_agent','f','f'),
  ('mychips','routes_v_query','inp_chad','mychips','tallies_v_paths','inp_chad','f','f'),
  ('mychips','routes_v_query','inp_cid','mychips','tallies_v_paths','inp_cid','f','f'),
  ('mychips','routes_v_query','margin','mychips','tallies_v_net','margin','f','f'),
  ('mychips','routes_v_query','max','mychips','tallies_v_net','max','f','f'),
  ('mychips','routes_v_query','min','mychips','tallies_v_net','min','f','f'),
  ('mychips','routes_v_query','nodes','mychips','tallies_v_paths','nodes','f','f'),
  ('mychips','routes_v_query','out','mychips','tallies_v_net','out','f','f'),
  ('mychips','routes_v_query','out_agent','mychips','tallies_v_paths','out_agent','f','f'),
  ('mychips','routes_v_query','out_chad','mychips','tallies_v_paths','out_chad','f','f'),
  ('mychips','routes_v_query','out_cid','mychips','tallies_v_paths','out_cid','f','f'),
  ('mychips','routes_v_query','pat','mychips','tallies_v_paths','pat','f','f'),
  ('mychips','routes_v_query','path','mychips','tallies_v_paths','path','f','f'),
  ('mychips','routes_v_query','reward','mychips','tallies','reward','f','f'),
  ('mychips','routes_v_query','rid','mychips','routes','rid','f','t'),
  ('mychips','routes_v_query','segment','mychips','tallies_v_paths','segment','f','f'),
  ('mychips','routes_v_query','seqs','mychips','tallies_v_paths','seqs','f','f'),
  ('mychips','routes_v_query','signs','mychips','tallies_v_paths','signs','f','f'),
  ('mychips','routes_v_query','sorter','mychips','routes_v_query','sorter','f','f'),
  ('mychips','routes_v_query','status','mychips','routes','status','f','f'),
  ('mychips','routes_v_query','top','mychips','tallies_v_paths','top','f','f'),
  ('mychips','routes_v_query','top_agent','mychips','tallies_v_paths','top_agent','f','f'),
  ('mychips','routes_v_query','top_chad','mychips','tallies_v_paths','top_chad','f','f'),
  ('mychips','routes_v_query','top_cid','mychips','tallies_v_paths','top_cid','f','f'),
  ('mychips','routes_v_query','top_tseq','mychips','tallies_v_paths','top_tseq','f','f'),
  ('mychips','routes_v_query','top_uuid','mychips','tallies_v_paths','top_uuid','f','f'),
  ('mychips','routes_v_query','uuids','mychips','tallies_v_paths','uuids','f','f'),
  ('mychips','routes_v_query','via_ent','mychips','routes','via_ent','f','f'),
  ('mychips','routes_v_query','via_tally','mychips','routes_v','via_tally','f','f'),
  ('mychips','routes_v_query','via_tseq','mychips','routes','via_tseq','f','f'),
  ('mychips','tallies','_last_chit','mychips','tallies','_last_chit','f','f'),
  ('mychips','tallies','bound','mychips','tallies','bound','f','f'),
  ('mychips','tallies','chain_conf','mychips','tallies','chain_conf','f','f'),
  ('mychips','tallies','chain_stat','mychips','tallies','chain_stat','f','f'),
  ('mychips','tallies','clutch','mychips','tallies','clutch','f','f'),
  ('mychips','tallies','comment','mychips','tallies','comment','f','f'),
  ('mychips','tallies','contract','mychips','tallies','contract','f','f'),
  ('mychips','tallies','crt_by','mychips','tallies','crt_by','f','f'),
  ('mychips','tallies','crt_date','mychips','tallies','crt_date','f','f'),
  ('mychips','tallies','digest','mychips','tallies','digest','f','f'),
  ('mychips','tallies','hold_agent','mychips','tallies','hold_agent','f','f'),
  ('mychips','tallies','hold_cert','mychips','tallies','hold_cert','f','f'),
  ('mychips','tallies','hold_cid','mychips','tallies','hold_cid','f','f'),
  ('mychips','tallies','hold_sets','mychips','tallies','hold_sets','f','f'),
  ('mychips','tallies','hold_sig','mychips','tallies','hold_sig','f','f'),
  ('mychips','tallies','hold_terms','mychips','tallies','hold_terms','f','f'),
  ('mychips','tallies','mod_by','mychips','tallies','mod_by','f','f'),
  ('mychips','tallies','mod_date','mychips','tallies','mod_date','f','f'),
  ('mychips','tallies','net_c','mychips','tallies','net_c','f','f'),
  ('mychips','tallies','net_pc','mychips','tallies','net_pc','f','f'),
  ('mychips','tallies','part_agent','mychips','tallies','part_agent','f','f'),
  ('mychips','tallies','part_cert','mychips','tallies','part_cert','f','f'),
  ('mychips','tallies','part_cid','mychips','tallies','part_cid','f','f'),
  ('mychips','tallies','part_ent','mychips','tallies','part_ent','f','f'),
  ('mychips','tallies','part_sets','mychips','tallies','part_sets','f','f'),
  ('mychips','tallies','part_sig','mychips','tallies','part_sig','f','f'),
  ('mychips','tallies','part_terms','mychips','tallies','part_terms','f','f'),
  ('mychips','tallies','request','mychips','tallies','request','f','f'),
  ('mychips','tallies','reward','mychips','tallies','reward','f','f'),
  ('mychips','tallies','status','mychips','tallies','status','f','f'),
  ('mychips','tallies','tally_date','mychips','tallies','tally_date','f','f'),
  ('mychips','tallies','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies','tally_seq','mychips','tallies','tally_seq','f','t'),
  ('mychips','tallies','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tallies','tally_uuid','mychips','tallies','tally_uuid','f','f'),
  ('mychips','tallies','target','mychips','tallies','target','f','f'),
  ('mychips','tallies','version','mychips','tallies','version','f','f'),
  ('mychips','tallies_v','ack_hash','mychips','tallies_v','ack_hash','f','f'),
  ('mychips','tallies_v','action','mychips','tallies_v','action','f','f'),
  ('mychips','tallies_v','bound','mychips','tallies','bound','f','f'),
  ('mychips','tallies_v','chain_conf','mychips','tallies','chain_conf','f','f'),
  ('mychips','tallies_v','chits','mychips','tallies_v','chits','f','f'),
  ('mychips','tallies_v','chits_p','mychips','tallies_v','chits_p','f','f'),
  ('mychips','tallies_v','clean','mychips','tallies_v','clean','f','f'),
  ('mychips','tallies_v','clutch','mychips','tallies','clutch','f','f'),
  ('mychips','tallies_v','comment','mychips','tallies','comment','f','f'),
  ('mychips','tallies_v','contract','mychips','tallies','contract','f','f'),
  ('mychips','tallies_v','crt_by','mychips','tallies','crt_by','f','f'),
  ('mychips','tallies_v','crt_date','mychips','tallies','crt_date','f','f'),
  ('mychips','tallies_v','digest','mychips','tallies','digest','f','f'),
  ('mychips','tallies_v','digest_v','mychips','tallies_v','digest_v','f','f'),
  ('mychips','tallies_v','hold_agent','mychips','tallies','hold_agent','f','f'),
  ('mychips','tallies_v','hold_cert','mychips','tallies','hold_cert','f','f'),
  ('mychips','tallies_v','hold_chad','mychips','tallies_v','hold_chad','f','f'),
  ('mychips','tallies_v','hold_cid','mychips','tallies','hold_cid','f','f'),
  ('mychips','tallies_v','hold_host','mychips','tallies_v','hold_host','f','f'),
  ('mychips','tallies_v','hold_port','mychips','tallies_v','hold_port','f','f'),
  ('mychips','tallies_v','hold_sets','mychips','tallies','hold_sets','f','f'),
  ('mychips','tallies_v','hold_sig','mychips','tallies','hold_sig','f','f'),
  ('mychips','tallies_v','hold_terms','mychips','tallies','hold_terms','f','f'),
  ('mychips','tallies_v','inside','mychips','tallies_v','inside','f','f'),
  ('mychips','tallies_v','json','mychips','agents_v','json','f','f'),
  ('mychips','tallies_v','json_core','mychips','tallies_v','json_core','f','f'),
  ('mychips','tallies_v','latest','mychips','tallies_v','latest','f','f'),
  ('mychips','tallies_v','liftable','mychips','tallies_v','liftable','f','f'),
  ('mychips','tallies_v','mod_by','mychips','tallies','mod_by','f','f'),
  ('mychips','tallies_v','mod_date','mychips','tallies','mod_date','f','f'),
  ('mychips','tallies_v','net','mychips','chits_v','net','f','f'),
  ('mychips','tallies_v','net_c','mychips','tallies','net_c','f','f'),
  ('mychips','tallies_v','net_p','mychips','tallies_v','net_p','f','f'),
  ('mychips','tallies_v','net_pc','mychips','tallies','net_pc','f','f'),
  ('mychips','tallies_v','part_addr','mychips','tallies_v','part_addr','f','f'),
  ('mychips','tallies_v','part_agent','mychips','tallies','part_agent','f','f'),
  ('mychips','tallies_v','part_cert','mychips','tallies','part_cert','f','f'),
  ('mychips','tallies_v','part_chad','mychips','tallies_v','part_chad','f','f'),
  ('mychips','tallies_v','part_cid','mychips','tallies','part_cid','f','f'),
  ('mychips','tallies_v','part_ent','mychips','tallies','part_ent','f','f'),
  ('mychips','tallies_v','part_host','mychips','tallies_v','part_host','f','f'),
  ('mychips','tallies_v','part_port','mychips','tallies_v','part_port','f','f'),
  ('mychips','tallies_v','part_sets','mychips','tallies','part_sets','f','f'),
  ('mychips','tallies_v','part_sig','mychips','tallies','part_sig','f','f'),
  ('mychips','tallies_v','part_terms','mychips','tallies','part_terms','f','f'),
  ('mychips','tallies_v','policy','mychips','tallies_v','policy','f','f'),
  ('mychips','tallies_v','request','mychips','tallies','request','f','f'),
  ('mychips','tallies_v','reward','mychips','tallies','reward','f','f'),
  ('mychips','tallies_v','state','mychips','tallies_v','state','f','f'),
  ('mychips','tallies_v','status','mychips','tallies','status','f','f'),
  ('mychips','tallies_v','tally_date','mychips','tallies','tally_date','f','f'),
  ('mychips','tallies_v','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies_v','tally_seq','mychips','tallies','tally_seq','f','t'),
  ('mychips','tallies_v','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tallies_v','tally_uuid','mychips','tallies','tally_uuid','f','f'),
  ('mychips','tallies_v','target','mychips','tallies','target','f','f'),
  ('mychips','tallies_v','version','mychips','tallies','version','f','f'),
  ('mychips','tallies_v_me','ack_hash','mychips','tallies_v','ack_hash','f','f'),
  ('mychips','tallies_v_me','action','mychips','tallies_v','action','f','f'),
  ('mychips','tallies_v_me','bound','mychips','tallies','bound','f','f'),
  ('mychips','tallies_v_me','chain_conf','mychips','tallies','chain_conf','f','f'),
  ('mychips','tallies_v_me','chits','mychips','tallies_v','chits','f','f'),
  ('mychips','tallies_v_me','chits_p','mychips','tallies_v','chits_p','f','f'),
  ('mychips','tallies_v_me','clean','mychips','tallies_v','clean','f','f'),
  ('mychips','tallies_v_me','clutch','mychips','tallies','clutch','f','f'),
  ('mychips','tallies_v_me','comment','mychips','tallies','comment','f','f'),
  ('mychips','tallies_v_me','contract','mychips','tallies','contract','f','f'),
  ('mychips','tallies_v_me','crt_by','mychips','tallies','crt_by','f','f'),
  ('mychips','tallies_v_me','crt_date','mychips','tallies','crt_date','f','f'),
  ('mychips','tallies_v_me','digest','mychips','tallies','digest','f','f'),
  ('mychips','tallies_v_me','digest_v','mychips','tallies_v','digest_v','f','f'),
  ('mychips','tallies_v_me','hold_agent','mychips','tallies','hold_agent','f','f'),
  ('mychips','tallies_v_me','hold_cert','mychips','tallies','hold_cert','f','f'),
  ('mychips','tallies_v_me','hold_chad','mychips','tallies_v','hold_chad','f','f'),
  ('mychips','tallies_v_me','hold_cid','mychips','tallies','hold_cid','f','f'),
  ('mychips','tallies_v_me','hold_host','mychips','tallies_v','hold_host','f','f'),
  ('mychips','tallies_v_me','hold_port','mychips','tallies_v','hold_port','f','f'),
  ('mychips','tallies_v_me','hold_sets','mychips','tallies','hold_sets','f','f'),
  ('mychips','tallies_v_me','hold_sig','mychips','tallies','hold_sig','f','f'),
  ('mychips','tallies_v_me','hold_terms','mychips','tallies','hold_terms','f','f'),
  ('mychips','tallies_v_me','inside','mychips','tallies_v','inside','f','f'),
  ('mychips','tallies_v_me','json','mychips','agents_v','json','f','f'),
  ('mychips','tallies_v_me','json_core','mychips','tallies_v','json_core','f','f'),
  ('mychips','tallies_v_me','latest','mychips','tallies_v','latest','f','f'),
  ('mychips','tallies_v_me','liftable','mychips','tallies_v','liftable','f','f'),
  ('mychips','tallies_v_me','mod_by','mychips','tallies','mod_by','f','f'),
  ('mychips','tallies_v_me','mod_date','mychips','tallies','mod_date','f','f'),
  ('mychips','tallies_v_me','net','mychips','chits_v','net','f','f'),
  ('mychips','tallies_v_me','net_c','mychips','tallies','net_c','f','f'),
  ('mychips','tallies_v_me','net_p','mychips','tallies_v','net_p','f','f'),
  ('mychips','tallies_v_me','net_pc','mychips','tallies','net_pc','f','f'),
  ('mychips','tallies_v_me','part_addr','mychips','tallies_v','part_addr','f','f'),
  ('mychips','tallies_v_me','part_agent','mychips','tallies','part_agent','f','f'),
  ('mychips','tallies_v_me','part_cert','mychips','tallies','part_cert','f','f'),
  ('mychips','tallies_v_me','part_chad','mychips','tallies_v','part_chad','f','f'),
  ('mychips','tallies_v_me','part_cid','mychips','tallies','part_cid','f','f'),
  ('mychips','tallies_v_me','part_ent','mychips','tallies','part_ent','f','f'),
  ('mychips','tallies_v_me','part_host','mychips','tallies_v','part_host','f','f'),
  ('mychips','tallies_v_me','part_port','mychips','tallies_v','part_port','f','f'),
  ('mychips','tallies_v_me','part_sets','mychips','tallies','part_sets','f','f'),
  ('mychips','tallies_v_me','part_sig','mychips','tallies','part_sig','f','f'),
  ('mychips','tallies_v_me','part_terms','mychips','tallies','part_terms','f','f'),
  ('mychips','tallies_v_me','policy','mychips','tallies_v','policy','f','f'),
  ('mychips','tallies_v_me','request','mychips','tallies','request','f','f'),
  ('mychips','tallies_v_me','reward','mychips','tallies','reward','f','f'),
  ('mychips','tallies_v_me','state','mychips','tallies_v','state','f','f'),
  ('mychips','tallies_v_me','status','mychips','tallies','status','f','f'),
  ('mychips','tallies_v_me','tally_date','mychips','tallies','tally_date','f','f'),
  ('mychips','tallies_v_me','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies_v_me','tally_seq','mychips','tallies','tally_seq','f','t'),
  ('mychips','tallies_v_me','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tallies_v_me','tally_uuid','mychips','tallies','tally_uuid','f','f'),
  ('mychips','tallies_v_me','target','mychips','tallies','target','f','f'),
  ('mychips','tallies_v_me','version','mychips','tallies','version','f','f'),
  ('mychips','tallies_v_net','bound','mychips','tallies','bound','f','f'),
  ('mychips','tallies_v_net','canlift','mychips','tallies_v_net','canlift','f','f'),
  ('mychips','tallies_v_net','inp','mychips','tallies_v_net','inp','f','f'),
  ('mychips','tallies_v_net','inv','mychips','tallies_v_net','inv','f','f'),
  ('mychips','tallies_v_net','margin','mychips','tallies_v_net','margin','f','f'),
  ('mychips','tallies_v_net','max','mychips','tallies_v_net','max','f','f'),
  ('mychips','tallies_v_net','min','mychips','tallies_v_net','min','f','f'),
  ('mychips','tallies_v_net','net_pc','mychips','tallies','net_pc','f','f'),
  ('mychips','tallies_v_net','out','mychips','tallies_v_net','out','f','f'),
  ('mychips','tallies_v_net','part','mychips','tallies_v_net','part','f','f'),
  ('mychips','tallies_v_net','part_ent','mychips','tallies','part_ent','f','f'),
  ('mychips','tallies_v_net','reward','mychips','tallies','reward','f','f'),
  ('mychips','tallies_v_net','sign','mychips','tallies_v_net','sign','f','f'),
  ('mychips','tallies_v_net','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies_v_net','tally_seq','mychips','tallies','tally_seq','f','t'),
  ('mychips','tallies_v_net','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tallies_v_net','target','mychips','tallies','target','f','f'),
  ('mychips','tallies_v_net','type','mychips','tallies_v_net','type','f','f'),
  ('mychips','tallies_v_net','uuid','mychips','tallies_v_net','uuid','f','f'),
  ('mychips','tallies_v_paths','at','mychips','tallies_v_paths','at','f','f'),
  ('mychips','tallies_v_paths','ath','mychips','tallies_v_paths','ath','f','f'),
  ('mychips','tallies_v_paths','bang','mychips','tallies_v_paths','bang','f','f'),
  ('mychips','tallies_v_paths','bot','mychips','tallies_v_paths','bot','f','f'),
  ('mychips','tallies_v_paths','bot_agent','mychips','tallies_v_paths','bot_agent','f','f'),
  ('mychips','tallies_v_paths','bot_chad','mychips','tallies_v_paths','bot_chad','f','f'),
  ('mychips','tallies_v_paths','bot_cid','mychips','tallies_v_paths','bot_cid','f','f'),
  ('mychips','tallies_v_paths','bot_tseq','mychips','tallies_v_paths','bot_tseq','f','f'),
  ('mychips','tallies_v_paths','bot_uuid','mychips','tallies_v_paths','bot_uuid','f','f'),
  ('mychips','tallies_v_paths','circuit','mychips','tallies_v_paths','circuit','f','f'),
  ('mychips','tallies_v_paths','edges','mychips','tallies_v_paths','edges','f','f'),
  ('mychips','tallies_v_paths','ents','mychips','tallies_v_paths','ents','f','f'),
  ('mychips','tallies_v_paths','fori','mychips','tallies_v_paths','fori','f','f'),
  ('mychips','tallies_v_paths','foro','mychips','tallies_v_paths','foro','f','f'),
  ('mychips','tallies_v_paths','inp','mychips','tallies_v_net','inp','f','f'),
  ('mychips','tallies_v_paths','inp_agent','mychips','tallies_v_paths','inp_agent','f','f'),
  ('mychips','tallies_v_paths','inp_chad','mychips','tallies_v_paths','inp_chad','f','f'),
  ('mychips','tallies_v_paths','inp_cid','mychips','tallies_v_paths','inp_cid','f','f'),
  ('mychips','tallies_v_paths','margin','mychips','tallies_v_net','margin','f','f'),
  ('mychips','tallies_v_paths','max','mychips','tallies_v_net','max','f','f'),
  ('mychips','tallies_v_paths','min','mychips','tallies_v_net','min','f','f'),
  ('mychips','tallies_v_paths','nodes','mychips','tallies_v_paths','nodes','f','f'),
  ('mychips','tallies_v_paths','out','mychips','tallies_v_net','out','f','f'),
  ('mychips','tallies_v_paths','out_agent','mychips','tallies_v_paths','out_agent','f','f'),
  ('mychips','tallies_v_paths','out_chad','mychips','tallies_v_paths','out_chad','f','f'),
  ('mychips','tallies_v_paths','out_cid','mychips','tallies_v_paths','out_cid','f','f'),
  ('mychips','tallies_v_paths','pat','mychips','tallies_v_paths','pat','f','f'),
  ('mychips','tallies_v_paths','path','mychips','tallies_v_paths','path','f','t'),
  ('mychips','tallies_v_paths','reward','mychips','tallies','reward','f','f'),
  ('mychips','tallies_v_paths','segment','mychips','tallies_v_paths','segment','f','f'),
  ('mychips','tallies_v_paths','seqs','mychips','tallies_v_paths','seqs','f','f'),
  ('mychips','tallies_v_paths','signs','mychips','tallies_v_paths','signs','f','f'),
  ('mychips','tallies_v_paths','top','mychips','tallies_v_paths','top','f','f'),
  ('mychips','tallies_v_paths','top_agent','mychips','tallies_v_paths','top_agent','f','f'),
  ('mychips','tallies_v_paths','top_chad','mychips','tallies_v_paths','top_chad','f','f'),
  ('mychips','tallies_v_paths','top_cid','mychips','tallies_v_paths','top_cid','f','f'),
  ('mychips','tallies_v_paths','top_tseq','mychips','tallies_v_paths','top_tseq','f','f'),
  ('mychips','tallies_v_paths','top_uuid','mychips','tallies_v_paths','top_uuid','f','f'),
  ('mychips','tallies_v_paths','uuids','mychips','tallies_v_paths','uuids','f','f'),
  ('mychips','tallies_v_sum','bounds','mychips','tallies_v_sum','bounds','f','f'),
  ('mychips','tallies_v_sum','client_agents','mychips','tallies_v_sum','client_agents','f','f'),
  ('mychips','tallies_v_sum','client_cids','mychips','tallies_v_sum','client_cids','f','f'),
  ('mychips','tallies_v_sum','clients','mychips','tallies_v_sum','clients','f','f'),
  ('mychips','tallies_v_sum','clutchs','mychips','tallies_v_sum','clutchs','f','f'),
  ('mychips','tallies_v_sum','foil_net','mychips','tallies_v_sum','foil_net','f','f'),
  ('mychips','tallies_v_sum','foil_nets','mychips','tallies_v_sum','foil_nets','f','f'),
  ('mychips','tallies_v_sum','foil_seqs','mychips','tallies_v_sum','foil_seqs','f','f'),
  ('mychips','tallies_v_sum','foil_uuids','mychips','tallies_v_sum','foil_uuids','f','f'),
  ('mychips','tallies_v_sum','foils','mychips','tallies_v_sum','foils','f','f'),
  ('mychips','tallies_v_sum','insides','mychips','tallies_v_sum','insides','f','f'),
  ('mychips','tallies_v_sum','json','mychips','agents_v','json','f','f'),
  ('mychips','tallies_v_sum','latest','mychips','tallies_v','latest','f','f'),
  ('mychips','tallies_v_sum','net','mychips','chits_v','net','f','f'),
  ('mychips','tallies_v_sum','nets','mychips','tallies_v_sum','nets','f','f'),
  ('mychips','tallies_v_sum','part_agents','mychips','tallies_v_sum','part_agents','f','f'),
  ('mychips','tallies_v_sum','part_cids','mychips','tallies_v_sum','part_cids','f','f'),
  ('mychips','tallies_v_sum','part_ents','mychips','tallies_v_sum','part_ents','f','f'),
  ('mychips','tallies_v_sum','policies','mychips','tallies_v_sum','policies','f','f'),
  ('mychips','tallies_v_sum','rewards','mychips','tallies_v_sum','rewards','f','f'),
  ('mychips','tallies_v_sum','seqs','mychips','tallies_v_sum','seqs','f','f'),
  ('mychips','tallies_v_sum','states','mychips','tallies_v_sum','states','f','f'),
  ('mychips','tallies_v_sum','stock_net','mychips','tallies_v_sum','stock_net','f','f'),
  ('mychips','tallies_v_sum','stock_nets','mychips','tallies_v_sum','stock_nets','f','f'),
  ('mychips','tallies_v_sum','stock_seqs','mychips','tallies_v_sum','stock_seqs','f','f'),
  ('mychips','tallies_v_sum','stock_uuids','mychips','tallies_v_sum','stock_uuids','f','f'),
  ('mychips','tallies_v_sum','stocks','mychips','tallies_v_sum','stocks','f','f'),
  ('mychips','tallies_v_sum','tallies','mychips','tallies_v_sum','tallies','f','f'),
  ('mychips','tallies_v_sum','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies_v_sum','targets','mychips','tallies_v_sum','targets','f','f'),
  ('mychips','tallies_v_sum','types','mychips','tallies_v_sum','types','f','f'),
  ('mychips','tallies_v_sum','uuids','mychips','tallies_v_sum','uuids','f','f'),
  ('mychips','tallies_v_sum','vendor_agents','mychips','tallies_v_sum','vendor_agents','f','f'),
  ('mychips','tallies_v_sum','vendor_cids','mychips','tallies_v_sum','vendor_cids','f','f'),
  ('mychips','tallies_v_sum','vendors','mychips','tallies_v_sum','vendors','f','f'),
  ('mychips','tally_tries','last','mychips','tally_tries','last','f','f'),
  ('mychips','tally_tries','tries','mychips','tally_tries','tries','f','f'),
  ('mychips','tally_tries','ttry_ent','mychips','tally_tries','ttry_ent','f','t'),
  ('mychips','tally_tries','ttry_seq','mychips','tally_tries','ttry_seq','f','t'),
  ('mychips','tokens','crt_by','mychips','tokens','crt_by','f','f'),
  ('mychips','tokens','crt_date','mychips','tokens','crt_date','f','f'),
  ('mychips','tokens','expires','mychips','tokens','expires','f','f'),
  ('mychips','tokens','mod_by','mychips','tokens','mod_by','f','f'),
  ('mychips','tokens','mod_date','mychips','tokens','mod_date','f','f'),
  ('mychips','tokens','reuse','mychips','tokens','reuse','f','f'),
  ('mychips','tokens','tally_seq','mychips','tokens','tally_seq','f','f'),
  ('mychips','tokens','token','mychips','tokens','token','f','f'),
  ('mychips','tokens','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','tokens','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','tokens','used','mychips','tokens','used','f','f'),
  ('mychips','tokens_v','chad','mychips','tokens_v','chad','f','f'),
  ('mychips','tokens_v','crt_by','mychips','tokens','crt_by','f','f'),
  ('mychips','tokens_v','crt_date','mychips','tokens','crt_date','f','f'),
  ('mychips','tokens_v','expired','mychips','tokens_v','expired','f','f'),
  ('mychips','tokens_v','expires','mychips','tokens','expires','f','f'),
  ('mychips','tokens_v','mod_by','mychips','tokens','mod_by','f','f'),
  ('mychips','tokens_v','mod_date','mychips','tokens','mod_date','f','f'),
  ('mychips','tokens_v','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','tokens_v','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','tokens_v','reuse','mychips','tokens','reuse','f','f'),
  ('mychips','tokens_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','tokens_v','tally_seq','mychips','tokens','tally_seq','f','f'),
  ('mychips','tokens_v','token','mychips','tokens','token','f','f'),
  ('mychips','tokens_v','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','tokens_v','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','tokens_v','used','mychips','tokens','used','f','f'),
  ('mychips','tokens_v','valid','mychips','tokens_v','valid','f','f'),
  ('mychips','tokens_v_me','chad','mychips','tokens_v','chad','f','f'),
  ('mychips','tokens_v_me','crt_by','mychips','tokens','crt_by','f','f'),
  ('mychips','tokens_v_me','crt_date','mychips','tokens','crt_date','f','f'),
  ('mychips','tokens_v_me','expired','mychips','tokens_v','expired','f','f'),
  ('mychips','tokens_v_me','expires','mychips','tokens','expires','f','f'),
  ('mychips','tokens_v_me','mod_by','mychips','tokens','mod_by','f','f'),
  ('mychips','tokens_v_me','mod_date','mychips','tokens','mod_date','f','f'),
  ('mychips','tokens_v_me','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','tokens_v_me','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','tokens_v_me','reuse','mychips','tokens','reuse','f','f'),
  ('mychips','tokens_v_me','std_name','base','ent_v','std_name','f','f'),
  ('mychips','tokens_v_me','tally_seq','mychips','tokens','tally_seq','f','f'),
  ('mychips','tokens_v_me','token','mychips','tokens','token','f','f'),
  ('mychips','tokens_v_me','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','tokens_v_me','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','tokens_v_me','used','mychips','tokens','used','f','f'),
  ('mychips','tokens_v_me','valid','mychips','tokens_v','valid','f','f'),
  ('mychips','users','_last_tally','mychips','users','_last_tally','f','f'),
  ('mychips','users','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','users','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','users','peer_named','mychips','users','peer_named','f','f'),
  ('mychips','users','peer_psig','mychips','users','peer_psig','f','f'),
  ('mychips','users','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users','user_ent','mychips','users','user_ent','f','t'),
  ('mychips','users','user_hid','mychips','users','user_hid','f','f'),
  ('mychips','users','user_host','mychips','users','user_host','f','f'),
  ('mychips','users','user_port','mychips','users','user_port','f','f'),
  ('mychips','users','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v','age','base','ent_v','age','f','f'),
  ('mychips','users_v','agent_host','mychips','agents','agent_host','f','f'),
  ('mychips','users_v','agent_ip','mychips','agents','agent_ip','f','f'),
  ('mychips','users_v','agent_key','mychips','agents','agent_key','f','f'),
  ('mychips','users_v','agent_port','mychips','agents','agent_port','f','f'),
  ('mychips','users_v','bank','base','ent','bank','f','f'),
  ('mychips','users_v','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v','conn_pub','base','ent','conn_pub','f','f'),
  ('mychips','users_v','country','base','ent','country','f','f'),
  ('mychips','users_v','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users_v','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v','ent_num','base','ent','ent_num','f','f'),
  ('mychips','users_v','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v','gender','base','ent','gender','f','f'),
  ('mychips','users_v','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','users_v','id','base','ent','id','f','t'),
  ('mychips','users_v','json','mychips','users_v','json','f','f'),
  ('mychips','users_v','marital','base','ent','marital','f','f'),
  ('mychips','users_v','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users_v','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users_v','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','users_v','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','users_v','peer_host','mychips','users_v','peer_host','f','f'),
  ('mychips','users_v','peer_named','mychips','users','peer_named','f','f'),
  ('mychips','users_v','peer_port','mychips','users_v','peer_port','f','f'),
  ('mychips','users_v','peer_psig','mychips','users','peer_psig','f','f'),
  ('mychips','users_v','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v','title','base','ent','title','f','f'),
  ('mychips','users_v','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v','user_ent','mychips','users','user_ent','f','f'),
  ('mychips','users_v','user_hid','mychips','users','user_hid','f','f'),
  ('mychips','users_v','user_host','mychips','users','user_host','f','f'),
  ('mychips','users_v','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v','username','base','ent','username','f','f'),
  ('mychips','users_v_flat','age','base','ent_v','age','f','f'),
  ('mychips','users_v_flat','agent_host','mychips','agents','agent_host','f','f'),
  ('mychips','users_v_flat','agent_ip','mychips','agents','agent_ip','f','f'),
  ('mychips','users_v_flat','agent_key','mychips','agents','agent_key','f','f'),
  ('mychips','users_v_flat','agent_port','mychips','agents','agent_port','f','f'),
  ('mychips','users_v_flat','bank','base','ent','bank','f','f'),
  ('mychips','users_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('mychips','users_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('mychips','users_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('mychips','users_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('mychips','users_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('mychips','users_v_flat','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v_flat','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('mychips','users_v_flat','conn_pub','base','ent','conn_pub','f','f'),
  ('mychips','users_v_flat','country','base','ent','country','f','f'),
  ('mychips','users_v_flat','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users_v_flat','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('mychips','users_v_flat','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v_flat','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v_flat','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v_flat','ent_num','base','ent','ent_num','f','f'),
  ('mychips','users_v_flat','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v_flat','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v_flat','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v_flat','gender','base','ent','gender','f','f'),
  ('mychips','users_v_flat','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','users_v_flat','id','base','ent','id','f','t'),
  ('mychips','users_v_flat','json','mychips','users_v','json','f','f'),
  ('mychips','users_v_flat','marital','base','ent','marital','f','f'),
  ('mychips','users_v_flat','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v_flat','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users_v_flat','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users_v_flat','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','users_v_flat','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','users_v_flat','peer_host','mychips','users_v','peer_host','f','f'),
  ('mychips','users_v_flat','peer_named','mychips','users','peer_named','f','f'),
  ('mychips','users_v_flat','peer_port','mychips','users_v','peer_port','f','f'),
  ('mychips','users_v_flat','peer_psig','mychips','users','peer_psig','f','f'),
  ('mychips','users_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('mychips','users_v_flat','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('mychips','users_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('mychips','users_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('mychips','users_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('mychips','users_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('mychips','users_v_flat','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v_flat','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v_flat','title','base','ent','title','f','f'),
  ('mychips','users_v_flat','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v_flat','user_ent','mychips','users','user_ent','f','t'),
  ('mychips','users_v_flat','user_hid','mychips','users','user_hid','f','f'),
  ('mychips','users_v_flat','user_host','mychips','users','user_host','f','f'),
  ('mychips','users_v_flat','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v_flat','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v_flat','username','base','ent','username','f','f'),
  ('mychips','users_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('mychips','users_v_me','age','base','ent_v','age','f','f'),
  ('mychips','users_v_me','agent_host','mychips','agents','agent_host','f','f'),
  ('mychips','users_v_me','agent_ip','mychips','agents','agent_ip','f','f'),
  ('mychips','users_v_me','agent_key','mychips','agents','agent_key','f','f'),
  ('mychips','users_v_me','agent_port','mychips','agents','agent_port','f','f'),
  ('mychips','users_v_me','bank','base','ent','bank','f','f'),
  ('mychips','users_v_me','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v_me','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v_me','conn_pub','base','ent','conn_pub','f','f'),
  ('mychips','users_v_me','country','base','ent','country','f','f'),
  ('mychips','users_v_me','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users_v_me','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users_v_me','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v_me','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v_me','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v_me','ent_num','base','ent','ent_num','f','f'),
  ('mychips','users_v_me','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v_me','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v_me','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v_me','gender','base','ent','gender','f','f'),
  ('mychips','users_v_me','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','users_v_me','id','base','ent','id','f','t'),
  ('mychips','users_v_me','json','mychips','users_v','json','f','f'),
  ('mychips','users_v_me','marital','base','ent','marital','f','f'),
  ('mychips','users_v_me','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v_me','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users_v_me','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users_v_me','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','users_v_me','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','users_v_me','peer_host','mychips','users_v','peer_host','f','f'),
  ('mychips','users_v_me','peer_named','mychips','users','peer_named','f','f'),
  ('mychips','users_v_me','peer_port','mychips','users_v','peer_port','f','f'),
  ('mychips','users_v_me','peer_psig','mychips','users','peer_psig','f','f'),
  ('mychips','users_v_me','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v_me','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v_me','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v_me','title','base','ent','title','f','f'),
  ('mychips','users_v_me','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v_me','user_ent','mychips','users','user_ent','f','f'),
  ('mychips','users_v_me','user_hid','mychips','users','user_hid','f','f'),
  ('mychips','users_v_me','user_host','mychips','users','user_host','f','f'),
  ('mychips','users_v_me','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v_me','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v_me','username','base','ent','username','f','f'),
  ('mychips','users_v_tallies','age','base','ent_v','age','f','f'),
  ('mychips','users_v_tallies','agent_host','mychips','agents','agent_host','f','f'),
  ('mychips','users_v_tallies','agent_ip','mychips','agents','agent_ip','f','f'),
  ('mychips','users_v_tallies','agent_key','mychips','agents','agent_key','f','f'),
  ('mychips','users_v_tallies','agent_port','mychips','agents','agent_port','f','f'),
  ('mychips','users_v_tallies','asset','mychips','users_v_tallies','asset','f','f'),
  ('mychips','users_v_tallies','assets','mychips','users_v_tallies','assets','f','f'),
  ('mychips','users_v_tallies','bank','base','ent','bank','f','f'),
  ('mychips','users_v_tallies','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v_tallies','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v_tallies','conn_pub','base','ent','conn_pub','f','f'),
  ('mychips','users_v_tallies','count','mychips','users_v_tallies','count','f','f'),
  ('mychips','users_v_tallies','country','base','ent','country','f','f'),
  ('mychips','users_v_tallies','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users_v_tallies','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users_v_tallies','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v_tallies','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v_tallies','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v_tallies','ent_num','base','ent','ent_num','f','f'),
  ('mychips','users_v_tallies','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v_tallies','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v_tallies','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v_tallies','gender','base','ent','gender','f','f'),
  ('mychips','users_v_tallies','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','users_v_tallies','id','base','ent','id','f','t'),
  ('mychips','users_v_tallies','json','mychips','users_v','json','f','f'),
  ('mychips','users_v_tallies','latest','mychips','tallies_v','latest','f','f'),
  ('mychips','users_v_tallies','liab','mychips','users_v_tallies','liab','f','f'),
  ('mychips','users_v_tallies','liabs','mychips','users_v_tallies','liabs','f','f'),
  ('mychips','users_v_tallies','marital','base','ent','marital','f','f'),
  ('mychips','users_v_tallies','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v_tallies','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users_v_tallies','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users_v_tallies','net','mychips','chits_v','net','f','f'),
  ('mychips','users_v_tallies','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','users_v_tallies','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','users_v_tallies','peer_host','mychips','users_v','peer_host','f','f'),
  ('mychips','users_v_tallies','peer_named','mychips','users','peer_named','f','f'),
  ('mychips','users_v_tallies','peer_port','mychips','users_v','peer_port','f','f'),
  ('mychips','users_v_tallies','peer_psig','mychips','users','peer_psig','f','f'),
  ('mychips','users_v_tallies','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v_tallies','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v_tallies','tallies','mychips','users_v_tallies','tallies','f','f'),
  ('mychips','users_v_tallies','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v_tallies','title','base','ent','title','f','f'),
  ('mychips','users_v_tallies','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v_tallies','user_ent','mychips','users','user_ent','f','t'),
  ('mychips','users_v_tallies','user_hid','mychips','users','user_hid','f','f'),
  ('mychips','users_v_tallies','user_host','mychips','users','user_host','f','f'),
  ('mychips','users_v_tallies','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v_tallies','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v_tallies','username','base','ent','username','f','f'),
  ('mychips','users_v_tallysum','bounds','mychips','tallies_v_sum','bounds','f','f'),
  ('mychips','users_v_tallysum','client_agents','mychips','tallies_v_sum','client_agents','f','f'),
  ('mychips','users_v_tallysum','client_cids','mychips','tallies_v_sum','client_cids','f','f'),
  ('mychips','users_v_tallysum','clients','mychips','tallies_v_sum','clients','f','f'),
  ('mychips','users_v_tallysum','clutchs','mychips','tallies_v_sum','clutchs','f','f'),
  ('mychips','users_v_tallysum','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v_tallysum','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v_tallysum','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v_tallysum','foil_seqs','mychips','tallies_v_sum','foil_seqs','f','f'),
  ('mychips','users_v_tallysum','foil_uuids','mychips','tallies_v_sum','foil_uuids','f','f'),
  ('mychips','users_v_tallysum','foils','mychips','tallies_v_sum','foils','f','f'),
  ('mychips','users_v_tallysum','id','base','ent','id','f','t'),
  ('mychips','users_v_tallysum','insides','mychips','tallies_v_sum','insides','f','f'),
  ('mychips','users_v_tallysum','json','mychips','agents_v','json','f','f'),
  ('mychips','users_v_tallysum','latest','mychips','tallies_v','latest','f','f'),
  ('mychips','users_v_tallysum','net','mychips','chits_v','net','f','f'),
  ('mychips','users_v_tallysum','nets','mychips','tallies_v_sum','nets','f','f'),
  ('mychips','users_v_tallysum','part_agents','mychips','tallies_v_sum','part_agents','f','f'),
  ('mychips','users_v_tallysum','part_cids','mychips','tallies_v_sum','part_cids','f','f'),
  ('mychips','users_v_tallysum','part_ents','mychips','tallies_v_sum','part_ents','f','f'),
  ('mychips','users_v_tallysum','peer_agent','mychips','users','peer_agent','f','f'),
  ('mychips','users_v_tallysum','peer_cid','mychips','users','peer_cid','f','f'),
  ('mychips','users_v_tallysum','peer_host','mychips','users_v','peer_host','f','f'),
  ('mychips','users_v_tallysum','peer_port','mychips','users_v','peer_port','f','f'),
  ('mychips','users_v_tallysum','policies','mychips','tallies_v_sum','policies','f','f'),
  ('mychips','users_v_tallysum','rewards','mychips','tallies_v_sum','rewards','f','f'),
  ('mychips','users_v_tallysum','seqs','mychips','tallies_v_sum','seqs','f','f'),
  ('mychips','users_v_tallysum','states','mychips','tallies_v_sum','states','f','f'),
  ('mychips','users_v_tallysum','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v_tallysum','stock_seqs','mychips','tallies_v_sum','stock_seqs','f','f'),
  ('mychips','users_v_tallysum','stock_uuids','mychips','tallies_v_sum','stock_uuids','f','f'),
  ('mychips','users_v_tallysum','stocks','mychips','tallies_v_sum','stocks','f','f'),
  ('mychips','users_v_tallysum','tallies','mychips','tallies_v_sum','tallies','f','f'),
  ('mychips','users_v_tallysum','targets','mychips','tallies_v_sum','targets','f','f'),
  ('mychips','users_v_tallysum','types','mychips','tallies_v_sum','types','f','f'),
  ('mychips','users_v_tallysum','user_ent','mychips','users','user_ent','f','t'),
  ('mychips','users_v_tallysum','uuids','mychips','tallies_v_sum','uuids','f','f'),
  ('mychips','users_v_tallysum','vendor_agents','mychips','tallies_v_sum','vendor_agents','f','f'),
  ('mychips','users_v_tallysum','vendor_cids','mychips','tallies_v_sum','vendor_cids','f','f'),
  ('mychips','users_v_tallysum','vendors','mychips','tallies_v_sum','vendors','f','f'),
  ('wm','column_ambig','col','wm','column_ambig','col','f','t'),
  ('wm','column_ambig','count','wm','column_ambig','count','f','f'),
  ('wm','column_ambig','natives','wm','column_ambig','natives','f','f'),
  ('wm','column_ambig','sch','wm','column_ambig','sch','f','t'),
  ('wm','column_ambig','spec','wm','column_ambig','spec','f','f'),
  ('wm','column_ambig','tab','wm','column_ambig','tab','f','t'),
  ('wm','column_data','cdt_col','wm','column_data','cdt_col','f','t'),
  ('wm','column_data','cdt_sch','wm','column_data','cdt_sch','f','t'),
  ('wm','column_data','cdt_tab','wm','column_data','cdt_tab','f','t'),
  ('wm','column_data','def','wm','column_data','def','f','f'),
  ('wm','column_data','field','wm','column_data','field','f','f'),
  ('wm','column_data','is_pkey','wm','column_data','is_pkey','f','f'),
  ('wm','column_data','length','wm','column_data','length','f','f'),
  ('wm','column_data','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_data','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_data','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_data','nonull','wm','column_data','nonull','f','f'),
  ('wm','column_data','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_data','tab_kind','wm','column_data','tab_kind','f','f'),
  ('wm','column_data','type','wm','column_data','type','f','f'),
  ('wm','column_def','col','wm','column_pub','col','f','t'),
  ('wm','column_def','obj','wm','column_pub','obj','f','f'),
  ('wm','column_def','val','wm','column_def','val','f','f'),
  ('wm','column_istyle','cs_col','wm','column_style','cs_col','f','t'),
  ('wm','column_istyle','cs_obj','wm','column_istyle','cs_obj','f','f'),
  ('wm','column_istyle','cs_sch','wm','column_style','cs_sch','f','t'),
  ('wm','column_istyle','cs_tab','wm','column_style','cs_tab','f','t'),
  ('wm','column_istyle','cs_value','wm','column_istyle','cs_value','f','f'),
  ('wm','column_istyle','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_istyle','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_istyle','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_istyle','nat_value','wm','column_istyle','nat_value','f','f'),
  ('wm','column_istyle','sw_name','wm','column_style','sw_name','f','t'),
  ('wm','column_istyle','sw_value','wm','column_style','sw_value','f','f'),
  ('wm','column_lang','col','wm','column_lang','col','f','t'),
  ('wm','column_lang','help','wm','column_text','help','t','f'),
  ('wm','column_lang','language','wm','column_text','language','t','f'),
  ('wm','column_lang','nat','wm','column_lang','nat','f','f'),
  ('wm','column_lang','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_lang','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_lang','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_lang','obj','wm','column_lang','obj','f','f'),
  ('wm','column_lang','sch','wm','column_lang','sch','f','t'),
  ('wm','column_lang','system','wm','column_lang','system','f','f'),
  ('wm','column_lang','tab','wm','column_lang','tab','f','t'),
  ('wm','column_lang','title','wm','column_text','title','t','f'),
  ('wm','column_lang','values','wm','column_lang','values','f','f'),
  ('wm','column_meta','col','wm','column_meta','col','f','t'),
  ('wm','column_meta','def','wm','column_data','def','f','f'),
  ('wm','column_meta','field','wm','column_data','field','f','f'),
  ('wm','column_meta','is_pkey','wm','column_data','is_pkey','f','f'),
  ('wm','column_meta','length','wm','column_data','length','f','f'),
  ('wm','column_meta','nat','wm','column_meta','nat','f','f'),
  ('wm','column_meta','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_meta','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_meta','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_meta','nonull','wm','column_data','nonull','f','f'),
  ('wm','column_meta','obj','wm','column_meta','obj','f','f'),
  ('wm','column_meta','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_meta','sch','wm','column_meta','sch','f','t'),
  ('wm','column_meta','styles','wm','column_meta','styles','f','f'),
  ('wm','column_meta','tab','wm','column_meta','tab','f','t'),
  ('wm','column_meta','type','wm','column_data','type','f','f'),
  ('wm','column_meta','values','wm','column_meta','values','f','f'),
  ('wm','column_native','cnt_col','wm','column_native','cnt_col','f','t'),
  ('wm','column_native','cnt_sch','wm','column_native','cnt_sch','f','t'),
  ('wm','column_native','cnt_tab','wm','column_native','cnt_tab','f','t'),
  ('wm','column_native','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_native','nat_exp','wm','column_native','nat_exp','f','f'),
  ('wm','column_native','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_native','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_native','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_pub','col','wm','column_pub','col','f','t'),
  ('wm','column_pub','def','wm','column_data','def','f','f'),
  ('wm','column_pub','field','wm','column_data','field','f','f'),
  ('wm','column_pub','help','wm','column_text','help','f','f'),
  ('wm','column_pub','is_pkey','wm','column_data','is_pkey','f','f'),
  ('wm','column_pub','language','wm','column_text','language','f','f'),
  ('wm','column_pub','length','wm','column_data','length','f','f'),
  ('wm','column_pub','nat','wm','column_pub','nat','f','f'),
  ('wm','column_pub','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_pub','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_pub','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_pub','nonull','wm','column_data','nonull','f','f'),
  ('wm','column_pub','obj','wm','column_pub','obj','f','f'),
  ('wm','column_pub','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_pub','sch','wm','column_pub','sch','f','t'),
  ('wm','column_pub','tab','wm','column_pub','tab','f','t'),
  ('wm','column_pub','title','wm','column_text','title','f','f'),
  ('wm','column_pub','type','wm','column_data','type','f','f'),
  ('wm','column_style','cs_col','wm','column_style','cs_col','f','t'),
  ('wm','column_style','cs_sch','wm','column_style','cs_sch','f','t'),
  ('wm','column_style','cs_tab','wm','column_style','cs_tab','f','t'),
  ('wm','column_style','sw_name','wm','column_style','sw_name','f','t'),
  ('wm','column_style','sw_value','wm','column_style','sw_value','f','f'),
  ('wm','column_text','ct_col','wm','column_text','ct_col','f','t'),
  ('wm','column_text','ct_sch','wm','column_text','ct_sch','f','t'),
  ('wm','column_text','ct_tab','wm','column_text','ct_tab','f','t'),
  ('wm','column_text','help','wm','column_text','help','f','f'),
  ('wm','column_text','language','wm','column_text','language','f','t'),
  ('wm','column_text','title','wm','column_text','title','f','f'),
  ('wm','fkey_data','conname','wm','fkey_data','conname','f','t'),
  ('wm','fkey_data','key','wm','fkey_data','key','f','f'),
  ('wm','fkey_data','keys','wm','fkey_data','keys','f','f'),
  ('wm','fkey_data','kyf_col','wm','fkey_data','kyf_col','f','f'),
  ('wm','fkey_data','kyf_field','wm','fkey_data','kyf_field','f','f'),
  ('wm','fkey_data','kyf_sch','wm','fkey_data','kyf_sch','f','f'),
  ('wm','fkey_data','kyf_tab','wm','fkey_data','kyf_tab','f','f'),
  ('wm','fkey_data','kyt_col','wm','fkey_data','kyt_col','f','f'),
  ('wm','fkey_data','kyt_field','wm','fkey_data','kyt_field','f','f'),
  ('wm','fkey_data','kyt_sch','wm','fkey_data','kyt_sch','f','f'),
  ('wm','fkey_data','kyt_tab','wm','fkey_data','kyt_tab','f','f'),
  ('wm','fkey_pub','conname','wm','fkey_data','conname','f','t'),
  ('wm','fkey_pub','fn_col','wm','fkey_pub','fn_col','f','f'),
  ('wm','fkey_pub','fn_obj','wm','fkey_pub','fn_obj','f','f'),
  ('wm','fkey_pub','fn_sch','wm','fkey_pub','fn_sch','f','f'),
  ('wm','fkey_pub','fn_tab','wm','fkey_pub','fn_tab','f','f'),
  ('wm','fkey_pub','ft_col','wm','fkey_pub','ft_col','f','f'),
  ('wm','fkey_pub','ft_obj','wm','fkey_pub','ft_obj','f','f'),
  ('wm','fkey_pub','ft_sch','wm','fkey_pub','ft_sch','f','f'),
  ('wm','fkey_pub','ft_tab','wm','fkey_pub','ft_tab','f','f'),
  ('wm','fkey_pub','key','wm','fkey_data','key','f','f'),
  ('wm','fkey_pub','keys','wm','fkey_data','keys','f','f'),
  ('wm','fkey_pub','tn_col','wm','fkey_pub','tn_col','f','f'),
  ('wm','fkey_pub','tn_obj','wm','fkey_pub','tn_obj','f','f'),
  ('wm','fkey_pub','tn_sch','wm','fkey_pub','tn_sch','f','f'),
  ('wm','fkey_pub','tn_tab','wm','fkey_pub','tn_tab','f','f'),
  ('wm','fkey_pub','tt_col','wm','fkey_pub','tt_col','f','f'),
  ('wm','fkey_pub','tt_obj','wm','fkey_pub','tt_obj','f','f'),
  ('wm','fkey_pub','tt_sch','wm','fkey_pub','tt_sch','f','f'),
  ('wm','fkey_pub','tt_tab','wm','fkey_pub','tt_tab','f','f'),
  ('wm','fkey_pub','unikey','wm','fkey_pub','unikey','f','f'),
  ('wm','fkeys_data','conname','wm','fkeys_data','conname','f','t'),
  ('wm','fkeys_data','ksf_cols','wm','fkeys_data','ksf_cols','f','f'),
  ('wm','fkeys_data','ksf_sch','wm','fkeys_data','ksf_sch','f','f'),
  ('wm','fkeys_data','ksf_tab','wm','fkeys_data','ksf_tab','f','f'),
  ('wm','fkeys_data','kst_cols','wm','fkeys_data','kst_cols','f','f'),
  ('wm','fkeys_data','kst_sch','wm','fkeys_data','kst_sch','f','f'),
  ('wm','fkeys_data','kst_tab','wm','fkeys_data','kst_tab','f','f'),
  ('wm','fkeys_pub','conname','wm','fkeys_data','conname','f','t'),
  ('wm','fkeys_pub','fn_obj','wm','fkeys_pub','fn_obj','f','f'),
  ('wm','fkeys_pub','fn_sch','wm','fkeys_pub','fn_sch','f','f'),
  ('wm','fkeys_pub','fn_tab','wm','fkeys_pub','fn_tab','f','f'),
  ('wm','fkeys_pub','ft_cols','wm','fkeys_pub','ft_cols','f','f'),
  ('wm','fkeys_pub','ft_obj','wm','fkeys_pub','ft_obj','f','f'),
  ('wm','fkeys_pub','ft_sch','wm','fkeys_pub','ft_sch','f','f'),
  ('wm','fkeys_pub','ft_tab','wm','fkeys_pub','ft_tab','f','f'),
  ('wm','fkeys_pub','tn_obj','wm','fkeys_pub','tn_obj','f','f'),
  ('wm','fkeys_pub','tn_sch','wm','fkeys_pub','tn_sch','f','f'),
  ('wm','fkeys_pub','tn_tab','wm','fkeys_pub','tn_tab','f','f'),
  ('wm','fkeys_pub','tt_cols','wm','fkeys_pub','tt_cols','f','f'),
  ('wm','fkeys_pub','tt_obj','wm','fkeys_pub','tt_obj','f','f'),
  ('wm','fkeys_pub','tt_sch','wm','fkeys_pub','tt_sch','f','f'),
  ('wm','fkeys_pub','tt_tab','wm','fkeys_pub','tt_tab','f','f'),
  ('wm','lang','bool','wm','lang','bool','f','f'),
  ('wm','message_text','code','wm','message_text','code','f','t'),
  ('wm','message_text','help','wm','message_text','help','f','f'),
  ('wm','message_text','language','wm','message_text','language','f','t'),
  ('wm','message_text','mt_sch','wm','message_text','mt_sch','f','t'),
  ('wm','message_text','mt_tab','wm','message_text','mt_tab','f','t'),
  ('wm','message_text','title','wm','message_text','title','f','f'),
  ('wm','objects','build','wm','objects','build','f','f'),
  ('wm','objects','built','wm','objects','built','f','f'),
  ('wm','objects','checkit','wm','objects','checkit','f','f'),
  ('wm','objects','col_data','wm','objects','col_data','f','f'),
  ('wm','objects','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects','del_idx','wm','objects','del_idx','f','f'),
  ('wm','objects','delta','wm','objects','delta','f','f'),
  ('wm','objects','deps','wm','objects','deps','f','f'),
  ('wm','objects','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects','grants','wm','objects','grants','f','f'),
  ('wm','objects','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects','module','wm','objects','module','f','f'),
  ('wm','objects','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v','build','wm','objects','build','f','f'),
  ('wm','objects_v','built','wm','objects','built','f','f'),
  ('wm','objects_v','checkit','wm','objects','checkit','f','f'),
  ('wm','objects_v','col_data','wm','objects','col_data','f','f'),
  ('wm','objects_v','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects_v','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects_v','del_idx','wm','objects','del_idx','f','f'),
  ('wm','objects_v','delta','wm','objects','delta','f','f'),
  ('wm','objects_v','deps','wm','objects','deps','f','f'),
  ('wm','objects_v','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects_v','grants','wm','objects','grants','f','f'),
  ('wm','objects_v','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects_v','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects_v','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects_v','module','wm','objects','module','f','f'),
  ('wm','objects_v','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v','object','wm','objects_v','object','f','f'),
  ('wm','objects_v','release','wm','releases','release','f','t'),
  ('wm','objects_v_dep','cycle','wm','objects_v_dep','cycle','f','f'),
  ('wm','objects_v_dep','depend','wm','objects_v_dep','depend','f','f'),
  ('wm','objects_v_dep','depth','wm','objects_v_dep','depth','f','f'),
  ('wm','objects_v_dep','fpath','wm','objects_v_dep','fpath','f','f'),
  ('wm','objects_v_dep','object','wm','objects_v_dep','object','f','f'),
  ('wm','objects_v_dep','od_nam','wm','objects_v_dep','od_nam','f','f'),
  ('wm','objects_v_dep','od_release','wm','objects_v_dep','od_release','f','f'),
  ('wm','objects_v_dep','od_typ','wm','objects_v_dep','od_typ','f','f'),
  ('wm','objects_v_dep','path','wm','objects_v_dep','path','f','f'),
  ('wm','objects_v_depth','build','wm','objects','build','f','f'),
  ('wm','objects_v_depth','built','wm','objects','built','f','f'),
  ('wm','objects_v_depth','checkit','wm','objects','checkit','f','f'),
  ('wm','objects_v_depth','col_data','wm','objects','col_data','f','f'),
  ('wm','objects_v_depth','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects_v_depth','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects_v_depth','del_idx','wm','objects','del_idx','f','f'),
  ('wm','objects_v_depth','delta','wm','objects','delta','f','f'),
  ('wm','objects_v_depth','deps','wm','objects','deps','f','f'),
  ('wm','objects_v_depth','depth','wm','objects_v_dep','depth','f','f'),
  ('wm','objects_v_depth','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects_v_depth','grants','wm','objects','grants','f','f'),
  ('wm','objects_v_depth','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects_v_depth','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects_v_depth','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects_v_depth','module','wm','objects','module','f','f'),
  ('wm','objects_v_depth','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v_depth','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v_depth','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v_depth','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v_depth','object','wm','objects_v','object','f','f'),
  ('wm','objects_v_depth','release','wm','releases','release','f','t'),
  ('wm','objects_v_max','build','wm','objects','build','f','f'),
  ('wm','objects_v_max','built','wm','objects','built','f','f'),
  ('wm','objects_v_max','checkit','wm','objects','checkit','f','f'),
  ('wm','objects_v_max','col_data','wm','objects','col_data','f','f'),
  ('wm','objects_v_max','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects_v_max','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects_v_max','del_idx','wm','objects','del_idx','f','f'),
  ('wm','objects_v_max','delta','wm','objects','delta','f','f'),
  ('wm','objects_v_max','deps','wm','objects','deps','f','f'),
  ('wm','objects_v_max','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects_v_max','grants','wm','objects','grants','f','f'),
  ('wm','objects_v_max','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects_v_max','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects_v_max','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects_v_max','module','wm','objects','module','f','f'),
  ('wm','objects_v_max','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v_max','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v_max','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v_max','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v_next','build','wm','objects','build','f','f'),
  ('wm','objects_v_next','built','wm','objects','built','f','f'),
  ('wm','objects_v_next','checkit','wm','objects','checkit','f','f'),
  ('wm','objects_v_next','col_data','wm','objects','col_data','f','f'),
  ('wm','objects_v_next','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects_v_next','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects_v_next','del_idx','wm','objects','del_idx','f','f'),
  ('wm','objects_v_next','delta','wm','objects','delta','f','f'),
  ('wm','objects_v_next','deps','wm','objects','deps','f','f'),
  ('wm','objects_v_next','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects_v_next','grants','wm','objects','grants','f','f'),
  ('wm','objects_v_next','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects_v_next','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects_v_next','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects_v_next','module','wm','objects','module','f','f'),
  ('wm','objects_v_next','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v_next','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v_next','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v_next','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v_next','object','wm','objects_v','object','f','f'),
  ('wm','objects_v_next','release','wm','releases','release','f','t'),
  ('wm','releases','committed','wm','releases','committed','f','f'),
  ('wm','releases','release','wm','releases','release','f','t'),
  ('wm','releases','sver_2','wm','releases','sver_2','f','f'),
  ('wm','role_members','level','wm','role_members','level','f','f'),
  ('wm','role_members','member','wm','role_members','member','f','t'),
  ('wm','role_members','priv','wm','role_members','priv','f','f'),
  ('wm','role_members','role','wm','role_members','role','f','t'),
  ('wm','table_data','cols','wm','table_data','cols','f','f'),
  ('wm','table_data','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_data','obj','wm','table_data','obj','f','f'),
  ('wm','table_data','pkey','wm','column_native','pkey','f','f'),
  ('wm','table_data','system','wm','table_data','system','f','f'),
  ('wm','table_data','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_data','td_sch','wm','table_data','td_sch','f','t'),
  ('wm','table_data','td_tab','wm','table_data','td_tab','f','t'),
  ('wm','table_lang','columns','wm','table_lang','columns','f','f'),
  ('wm','table_lang','help','wm','table_text','help','t','f'),
  ('wm','table_lang','language','wm','table_text','language','t','t'),
  ('wm','table_lang','messages','wm','table_lang','messages','f','f'),
  ('wm','table_lang','obj','wm','table_lang','obj','f','f'),
  ('wm','table_lang','sch','wm','column_lang','sch','f','t'),
  ('wm','table_lang','tab','wm','column_lang','tab','f','t'),
  ('wm','table_lang','title','wm','table_text','title','t','f'),
  ('wm','table_meta','cols','wm','table_data','cols','f','f'),
  ('wm','table_meta','columns','wm','table_meta','columns','f','f'),
  ('wm','table_meta','fkeys','wm','table_meta','fkeys','f','f'),
  ('wm','table_meta','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_meta','obj','wm','table_meta','obj','f','f'),
  ('wm','table_meta','pkey','wm','table_data','pkey','t','f'),
  ('wm','table_meta','sch','wm','column_meta','sch','f','t'),
  ('wm','table_meta','styles','wm','column_meta','styles','f','f'),
  ('wm','table_meta','system','wm','table_data','system','f','f'),
  ('wm','table_meta','tab','wm','column_meta','tab','f','t'),
  ('wm','table_meta','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_pub','cols','wm','table_data','cols','f','f'),
  ('wm','table_pub','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_pub','help','wm','table_text','help','f','f'),
  ('wm','table_pub','language','wm','table_text','language','f','t'),
  ('wm','table_pub','obj','wm','table_pub','obj','f','f'),
  ('wm','table_pub','pkey','wm','column_native','pkey','f','f'),
  ('wm','table_pub','sch','wm','table_pub','sch','f','t'),
  ('wm','table_pub','system','wm','table_data','system','f','f'),
  ('wm','table_pub','tab','wm','table_pub','tab','f','t'),
  ('wm','table_pub','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_pub','title','wm','table_text','title','f','f'),
  ('wm','table_style','inherit','wm','table_style','inherit','f','f'),
  ('wm','table_style','sw_name','wm','table_style','sw_name','f','t'),
  ('wm','table_style','sw_value','wm','table_style','sw_value','f','f'),
  ('wm','table_style','ts_sch','wm','table_style','ts_sch','f','t'),
  ('wm','table_style','ts_tab','wm','table_style','ts_tab','f','t'),
  ('wm','table_text','help','wm','table_text','help','f','f'),
  ('wm','table_text','language','wm','table_text','language','f','t'),
  ('wm','table_text','title','wm','table_text','title','f','f'),
  ('wm','table_text','tt_sch','wm','table_text','tt_sch','f','t'),
  ('wm','table_text','tt_tab','wm','table_text','tt_tab','f','t'),
  ('wm','value_text','help','wm','value_text','help','f','f'),
  ('wm','value_text','language','wm','value_text','language','f','t'),
  ('wm','value_text','title','wm','value_text','title','f','f'),
  ('wm','value_text','value','wm','value_text','value','f','t'),
  ('wm','value_text','vt_col','wm','value_text','vt_col','f','t'),
  ('wm','value_text','vt_sch','wm','value_text','vt_sch','f','t'),
  ('wm','value_text','vt_tab','wm','value_text','vt_tab','f','t'),
  ('wm','view_column_usage','column_name','information_schema','view_column_usage','column_name','f','f'),
  ('wm','view_column_usage','table_catalog','information_schema','view_column_usage','table_catalog','f','f'),
  ('wm','view_column_usage','table_name','information_schema','view_column_usage','table_name','f','f'),
  ('wm','view_column_usage','table_schema','information_schema','view_column_usage','table_schema','f','f'),
  ('wm','view_column_usage','view_catalog','information_schema','view_column_usage','view_catalog','f','f'),
  ('wm','view_column_usage','view_name','information_schema','view_column_usage','view_name','f','t'),
  ('wm','view_column_usage','view_schema','information_schema','view_column_usage','view_schema','f','t'),
  ('wylib','data','access','wylib','data','access','f','f'),
  ('wylib','data','component','wylib','data','component','f','f'),
  ('wylib','data','crt_by','wylib','data','crt_by','f','f'),
  ('wylib','data','crt_date','wylib','data','crt_date','f','f'),
  ('wylib','data','data','wylib','data','data','f','f'),
  ('wylib','data','descr','wylib','data','descr','f','f'),
  ('wylib','data','mod_by','wylib','data','mod_by','f','f'),
  ('wylib','data','mod_date','wylib','data','mod_date','f','f'),
  ('wylib','data','name','wylib','data','name','f','f'),
  ('wylib','data','owner','wylib','data','owner','f','f'),
  ('wylib','data','ruid','wylib','data','ruid','f','t'),
  ('wylib','data_v','access','wylib','data','access','f','f'),
  ('wylib','data_v','component','wylib','data','component','f','f'),
  ('wylib','data_v','crt_by','wylib','data','crt_by','f','f'),
  ('wylib','data_v','crt_date','wylib','data','crt_date','f','f'),
  ('wylib','data_v','data','wylib','data','data','f','f'),
  ('wylib','data_v','descr','wylib','data','descr','f','f'),
  ('wylib','data_v','mod_by','wylib','data','mod_by','f','f'),
  ('wylib','data_v','mod_date','wylib','data','mod_date','f','f'),
  ('wylib','data_v','name','wylib','data','name','f','f'),
  ('wylib','data_v','own_name','wylib','data_v','own_name','f','f'),
  ('wylib','data_v','owner','wylib','data','owner','f','f'),
  ('wylib','data_v','ruid','wylib','data','ruid','f','t');

--Initialization:
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values
 ('AF','Afghanistan','Kabul','AFN','Afghani','+93','AFG','.af'),
 ('AL','Albania','Tirana','ALL','Lek','+355','ALB','.al'),
 ('DZ','Algeria','Algiers','DZD','Dinar','+213','DZA','.dz'),
 ('AD','Andorra','Andorra la Vella','EUR','Euro','+376','AND','.ad'),
 ('AO','Angola','Luanda','AOA','Kwanza','+244','AGO','.ao'),
 ('AG','Antigua and Barbuda','Saint John''s','XCD','Dollar','+1-268','ATG','.ag'),
 ('AR','Argentina','Buenos Aires','ARS','Peso','+54','ARG','.ar'),
 ('AM','Armenia','Yerevan','AMD','Dram','+374','ARM','.am'),
 ('AU','Australia','Canberra','AUD','Dollar','+61','AUS','.au'),
 ('AT','Austria','Vienna','EUR','Euro','+43','AUT','.at'),
 ('AZ','Azerbaijan','Baku','AZN','Manat','+994','AZE','.az'),
 ('BS','Bahamas, The','Nassau','BSD','Dollar','+1-242','BHS','.bs'),
 ('BH','Bahrain','Manama','BHD','Dinar','+973','BHR','.bh'),
 ('BD','Bangladesh','Dhaka','BDT','Taka','+880','BGD','.bd'),
 ('BB','Barbados','Bridgetown','BBD','Dollar','+1-246','BRB','.bb'),
 ('BY','Belarus','Minsk','BYR','Ruble','+375','BLR','.by'),
 ('BE','Belgium','Brussels','EUR','Euro','+32','BEL','.be'),
 ('BZ','Belize','Belmopan','BZD','Dollar','+501','BLZ','.bz'),
 ('BJ','Benin','Porto-Novo','XOF','Franc','+229','BEN','.bj'),
 ('BT','Bhutan','Thimphu','BTN','Ngultrum','+975','BTN','.bt'),
 ('BO','Bolivia','La Paz (administrative/legislative) and Sucre (judical)','BOB','Boliviano','+591','BOL','.bo'),
 ('BA','Bosnia and Herzegovina','Sarajevo','BAM','Marka','+387','BIH','.ba'),
 ('BW','Botswana','Gaborone','BWP','Pula','+267','BWA','.bw'),
 ('BR','Brazil','Brasilia','BRL','Real','+55','BRA','.br'),
 ('BN','Brunei','Bandar Seri Begawan','BND','Dollar','+673','BRN','.bn'),
 ('BG','Bulgaria','Sofia','BGN','Lev','+359','BGR','.bg'),
 ('BF','Burkina Faso','Ouagadougou','XOF','Franc','+226','BFA','.bf'),
 ('BI','Burundi','Bujumbura','BIF','Franc','+257','BDI','.bi'),
 ('KH','Cambodia','Phnom Penh','KHR','Riels','+855','KHM','.kh'),
 ('CM','Cameroon','Yaounde','XAF','Franc','+237','CMR','.cm'),
 ('CA','Canada','Ottawa','CAD','Dollar','+1','CAN','.ca'),
 ('CV','Cape Verde','Praia','CVE','Escudo','+238','CPV','.cv'),
 ('CF','Central African Republic','Bangui','XAF','Franc','+236','CAF','.cf'),
 ('TD','Chad','N''Djamena','XAF','Franc','+235','TCD','.td'),
 ('CL','Chile','Santiago (administrative/judical) and Valparaiso (legislative)','CLP','Peso','+56','CHL','.cl'),
 ('CN','China, People''s Republic of','Beijing','CNY','Yuan Renminbi','+86','CHN','.cn'),
 ('CO','Colombia','Bogota','COP','Peso','+57','COL','.co'),
 ('KM','Comoros','Moroni','KMF','Franc','+269','COM','.km'),
 ('CD','Congo, Democratic Republic of the (Congo � Kinshasa)','Kinshasa','CDF','Franc','+243','COD','.cd'),
 ('CG','Congo, Republic of the (Congo � Brazzaville)','Brazzaville','XAF','Franc','+242','COG','.cg'),
 ('CR','Costa Rica','San Jose','CRC','Colon','+506','CRI','.cr'),
 ('CI','Cote d''Ivoire (Ivory Coast)','Yamoussoukro','XOF','Franc','+225','CIV','.ci'),
 ('HR','Croatia','Zagreb','HRK','Kuna','+385','HRV','.hr'),
 ('CU','Cuba','Havana','CUP','Peso','+53','CUB','.cu'),
 ('CY','Cyprus','Nicosia','CYP','Pound','+357','CYP','.cy'),
 ('CZ','Czech Republic','Prague','CZK','Koruna','+420','CZE','.cz'),
 ('DK','Denmark','Copenhagen','DKK','Krone','+45','DNK','.dk'),
 ('DJ','Djibouti','Djibouti','DJF','Franc','+253','DJI','.dj'),
 ('DM','Dominica','Roseau','XCD','Dollar','+1-767','DMA','.dm'),
 ('DO','Dominican Republic','Santo Domingo','DOP','Peso','+1-809','DOM','.do'),
 ('EC','Ecuador','Quito','USD','Dollar','+593','ECU','.ec'),
 ('EG','Egypt','Cairo','EGP','Pound','+20','EGY','.eg'),
 ('SV','El Salvador','San Salvador','USD','Dollar','+503','SLV','.sv'),
 ('GQ','Equatorial Guinea','Malabo','XAF','Franc','+240','GNQ','.gq'),
 ('ER','Eritrea','Asmara','ERN','Nakfa','+291','ERI','.er'),
 ('EE','Estonia','Tallinn','EEK','Kroon','+372','EST','.ee'),
 ('ET','Ethiopia','Addis Ababa','ETB','Birr','+251','ETH','.et'),
 ('FJ','Fiji','Suva','FJD','Dollar','+679','FJI','.fj'),
 ('FI','Finland','Helsinki','EUR','Euro','+358','FIN','.fi'),
 ('FR','France','Paris','EUR','Euro','+33','FRA','.fr'),
 ('GA','Gabon','Libreville','XAF','Franc','+241','GAB','.ga'),
 ('GM','Gambia, The','Banjul','GMD','Dalasi','+220','GMB','.gm'),
 ('GE','Georgia','Tbilisi','GEL','Lari','+995','GEO','.ge'),
 ('DE','Germany','Berlin','EUR','Euro','+49','DEU','.de'),
 ('GH','Ghana','Accra','GHS','Cedi','+233','GHA','.gh'),
 ('GR','Greece','Athens','EUR','Euro','+30','GRC','.gr'),
 ('GD','Grenada','Saint George''s','XCD','Dollar','+1-473','GRD','.gd'),
 ('GT','Guatemala','Guatemala','GTQ','Quetzal','+502','GTM','.gt'),
 ('GN','Guinea','Conakry','GNF','Franc','+224','GIN','.gn'),
 ('GW','Guinea-Bissau','Bissau','XOF','Franc','+245','GNB','.gw'),
 ('GY','Guyana','Georgetown','GYD','Dollar','+592','GUY','.gy'),
 ('HT','Haiti','Port-au-Prince','HTG','Gourde','+509','HTI','.ht'),
 ('HN','Honduras','Tegucigalpa','HNL','Lempira','+504','HND','.hn'),
 ('HU','Hungary','Budapest','HUF','Forint','+36','HUN','.hu'),
 ('IS','Iceland','Reykjavik','ISK','Krona','+354','ISL','.is'),
 ('IN','India','New Delhi','INR','Rupee','+91','IND','.in'),
 ('ID','Indonesia','Jakarta','IDR','Rupiah','+62','IDN','.id'),
 ('IR','Iran','Tehran','IRR','Rial','+98','IRN','.ir'),
 ('IQ','Iraq','Baghdad','IQD','Dinar','+964','IRQ','.iq'),
 ('IE','Ireland','Dublin','EUR','Euro','+353','IRL','.ie'),
 ('IL','Israel','Jerusalem','ILS','Shekel','+972','ISR','.il'),
 ('IT','Italy','Rome','EUR','Euro','+39','ITA','.it'),
 ('JM','Jamaica','Kingston','JMD','Dollar','+1-876','JAM','.jm'),
 ('JP','Japan','Tokyo','JPY','Yen','+81','JPN','.jp'),
 ('JO','Jordan','Amman','JOD','Dinar','+962','JOR','.jo'),
 ('KZ','Kazakhstan','Astana','KZT','Tenge','+7','KAZ','.kz'),
 ('KE','Kenya','Nairobi','KES','Shilling','+254','KEN','.ke'),
 ('KI','Kiribati','Tarawa','AUD','Dollar','+686','KIR','.ki'),
 ('KP','Korea, Democratic People''s Republic of (North Korea)','Pyongyang','KPW','Won','+850','PRK','.kp'),
 ('KR','Korea, Republic of  (South Korea)','Seoul','KRW','Won','+82','KOR','.kr'),
 ('KW','Kuwait','Kuwait','KWD','Dinar','+965','KWT','.kw'),
 ('KG','Kyrgyzstan','Bishkek','KGS','Som','+996','KGZ','.kg'),
 ('LA','Laos','Vientiane','LAK','Kip','+856','LAO','.la'),
 ('LV','Latvia','Riga','LVL','Lat','+371','LVA','.lv'),
 ('LB','Lebanon','Beirut','LBP','Pound','+961','LBN','.lb'),
 ('LS','Lesotho','Maseru','LSL','Loti','+266','LSO','.ls'),
 ('LR','Liberia','Monrovia','LRD','Dollar','+231','LBR','.lr'),
 ('LY','Libya','Tripoli','LYD','Dinar','+218','LBY','.ly'),
 ('LI','Liechtenstein','Vaduz','CHF','Franc','+423','LIE','.li'),
 ('LT','Lithuania','Vilnius','LTL','Litas','+370','LTU','.lt'),
 ('LU','Luxembourg','Luxembourg','EUR','Euro','+352','LUX','.lu'),
 ('MK','Macedonia','Skopje','MKD','Denar','+389','MKD','.mk'),
 ('MG','Madagascar','Antananarivo','MGA','Ariary','+261','MDG','.mg'),
 ('MW','Malawi','Lilongwe','MWK','Kwacha','+265','MWI','.mw'),
 ('MY','Malaysia','Kuala Lumpur (legislative/judical) and Putrajaya (administrative)','MYR','Ringgit','+60','MYS','.my'),
 ('MV','Maldives','Male','MVR','Rufiyaa','+960','MDV','.mv'),
 ('ML','Mali','Bamako','XOF','Franc','+223','MLI','.ml'),
 ('MT','Malta','Valletta','MTL','Lira','+356','MLT','.mt'),
 ('MH','Marshall Islands','Majuro','USD','Dollar','+692','MHL','.mh'),
 ('MR','Mauritania','Nouakchott','MRO','Ouguiya','+222','MRT','.mr'),
 ('MU','Mauritius','Port Louis','MUR','Rupee','+230','MUS','.mu'),
 ('MX','Mexico','Mexico','MXN','Peso','+52','MEX','.mx'),
 ('FM','Micronesia','Palikir','USD','Dollar','+691','FSM','.fm'),
 ('MD','Moldova','Chisinau','MDL','Leu','+373','MDA','.md'),
 ('MC','Monaco','Monaco','EUR','Euro','+377','MCO','.mc'),
 ('MN','Mongolia','Ulaanbaatar','MNT','Tugrik','+976','MNG','.mn'),
 ('MA','Morocco','Rabat','MAD','Dirham','+212','MAR','.ma'),
 ('MZ','Mozambique','Maputo','MZM','Meticail','+258','MOZ','.mz'),
 ('MM','Myanmar (Burma)','Naypyidaw','MMK','Kyat','+95','MMR','.mm'),
 ('NA','Namibia','Windhoek','NAD','Dollar','+264','NAM','.na'),
 ('NR','Nauru','Yaren','AUD','Dollar','+674','NRU','.nr'),
 ('NP','Nepal','Kathmandu','NPR','Rupee','+977','NPL','.np'),
 ('NL','Netherlands','Amsterdam (administrative) and The Hague (legislative/judical)','EUR','Euro','+31','NLD','.nl'),
 ('NZ','New Zealand','Wellington','NZD','Dollar','+64','NZL','.nz'),
 ('NI','Nicaragua','Managua','NIO','Cordoba','+505','NIC','.ni'),
 ('NE','Niger','Niamey','XOF','Franc','+227','NER','.ne'),
 ('NG','Nigeria','Abuja','NGN','Naira','+234','NGA','.ng'),
 ('NO','Norway','Oslo','NOK','Krone','+47','NOR','.no'),
 ('OM','Oman','Muscat','OMR','Rial','+968','OMN','.om'),
 ('PK','Pakistan','Islamabad','PKR','Rupee','+92','PAK','.pk'),
 ('PW','Palau','Melekeok','USD','Dollar','+680','PLW','.pw'),
 ('PA','Panama','Panama','PAB','Balboa','+507','PAN','.pa'),
 ('PG','Papua New Guinea','Port Moresby','PGK','Kina','+675','PNG','.pg'),
 ('PY','Paraguay','Asuncion','PYG','Guarani','+595','PRY','.py'),
 ('PE','Peru','Lima','PEN','Sol','+51','PER','.pe'),
 ('PH','Philippines','Manila','PHP','Peso','+63','PHL','.ph'),
 ('PL','Poland','Warsaw','PLN','Zloty','+48','POL','.pl'),
 ('PT','Portugal','Lisbon','EUR','Euro','+351','PRT','.pt'),
 ('QA','Qatar','Doha','QAR','Rial','+974','QAT','.qa'),
 ('RO','Romania','Bucharest','RON','Leu','+40','ROU','.ro'),
 ('RW','Rwanda','Kigali','RWF','Franc','+250','RWA','.rw'),
 ('KN','Saint Kitts and Nevis','Basseterre','XCD','Dollar','+1-869','KNA','.kn'),
 ('LC','Saint Lucia','Castries','XCD','Dollar','+1-758','LCA','.lc'),
 ('VC','Saint Vincent and the Grenadines','Kingstown','XCD','Dollar','+1-784','VCT','.vc'),
 ('WS','Samoa','Apia','WST','Tala','+685','WSM','.ws'),
 ('SM','San Marino','San Marino','EUR','Euro','+378','SMR','.sm'),
 ('ST','Sao Tome and Principe','Sao Tome','STD','Dobra','+239','STP','.st'),
 ('SA','Saudi Arabia','Riyadh','SAR','Rial','+966','SAU','.sa'),
 ('SN','Senegal','Dakar','XOF','Franc','+221','SEN','.sn'),
 ('SC','Seychelles','Victoria','SCR','Rupee','+248','SYC','.sc'),
 ('SL','Sierra Leone','Freetown','SLL','Leone','+232','SLE','.sl'),
 ('SG','Singapore','Singapore','SGD','Dollar','+65','SGP','.sg'),
 ('SK','Slovakia','Bratislava','SKK','Koruna','+421','SVK','.sk'),
 ('SI','Slovenia','Ljubljana','EUR','Euro','+386','SVN','.si'),
 ('SB','Solomon Islands','Honiara','SBD','Dollar','+677','SLB','.sb'),
 ('SO','Somalia','Mogadishu','SOS','Shilling','+252','SOM','.so'),
 ('ZA','South Africa','Pretoria (administrative), Cape Town (legislative), and Bloemfontein (judical)','ZAR','Rand','+27','ZAF','.za'),
 ('ES','Spain','Madrid','EUR','Euro','+34','ESP','.es'),
 ('LK','Sri Lanka','Colombo (administrative/judical) and Sri Jayewardenepura Kotte (legislative)','LKR','Rupee','+94','LKA','.lk'),
 ('SD','Sudan','Khartoum','SDG','Pound','+249','SDN','.sd'),
 ('SR','Suriname','Paramaribo','SRD','Dollar','+597','SUR','.sr'),
 ('SZ','Swaziland','Mbabane (administrative) and Lobamba (legislative)','SZL','Lilangeni','+268','SWZ','.sz'),
 ('SE','Sweden','Stockholm','SEK','Kronoa','+46','SWE','.se'),
 ('CH','Switzerland','Bern','CHF','Franc','+41','CHE','.ch'),
 ('SY','Syria','Damascus','SYP','Pound','+963','SYR','.sy'),
 ('TJ','Tajikistan','Dushanbe','TJS','Somoni','+992','TJK','.tj'),
 ('TZ','Tanzania','Dar es Salaam (administrative/judical) and Dodoma (legislative)','TZS','Shilling','+255','TZA','.tz'),
 ('TH','Thailand','Bangkok','THB','Baht','+66','THA','.th'),
 ('TG','Togo','Lome','XOF','Franc','+228','TGO','.tg'),
 ('TO','Tonga','Nuku''alofa','TOP','Pa''anga','+676','TON','.to'),
 ('TT','Trinidad and Tobago','Port-of-Spain','TTD','Dollar','+1-868','TTO','.tt'),
 ('TN','Tunisia','Tunis','TND','Dinar','+216','TUN','.tn'),
 ('TR','Turkey','Ankara','TRY','Lira','+90','TUR','.tr'),
 ('TM','Turkmenistan','Ashgabat','TMM','Manat','+993','TKM','.tm'),
 ('TV','Tuvalu','Funafuti','AUD','Dollar','+688','TUV','.tv'),
 ('UG','Uganda','Kampala','UGX','Shilling','+256','UGA','.ug'),
 ('UA','Ukraine','Kiev','UAH','Hryvnia','+380','UKR','.ua'),
 ('AE','United Arab Emirates','Abu Dhabi','AED','Dirham','+971','ARE','.ae'),
 ('GB','United Kingdom','London','GBP','Pound','+44','GBR','.uk'),
 ('US','United States','Washington','USD','Dollar','+1','USA','.us'),
 ('UY','Uruguay','Montevideo','UYU','Peso','+598','URY','.uy'),
 ('UZ','Uzbekistan','Tashkent','UZS','Som','+998','UZB','.uz'),
 ('VU','Vanuatu','Port-Vila','VUV','Vatu','+678','VUT','.vu'),
 ('VA','Vatican City','Vatican City','EUR','Euro','+379','VAT','.va'),
 ('VE','Venezuela','Caracas','VEB','Bolivar','+58','VEN','.ve'),
 ('VN','Vietnam','Hanoi','VND','Dong','+84','VNM','.vn'),
 ('YE','Yemen','Sanaa','YER','Rial','+967','YEM','.ye'),
 ('ZM','Zambia','Lusaka','ZMK','Kwacha','+260','ZMB','.zm'),
 ('ZW','Zimbabwe','Harare','ZWD','Dollar','+263','ZWE','.zw'),
 ('TW','China, Republic of (Taiwan)','Taipei','TWD','Dollar','+886','TWN','.tw'),
 ('CX','Christmas Island','The Settlement (Flying Fish Cove)','AUD','Dollar','+61','CXR','.cx'),
 ('CC','Cocos (Keeling) Islands','West Island','AUD','Dollar','+61','CCK','.cc'),
 ('HM','Heard Island and McDonald Islands','','','','','HMD','.hm'),
 ('NF','Norfolk Island','Kingston','AUD','Dollar','+672','NFK','.nf'),
 ('NC','New Caledonia','Noumea','XPF','Franc','+687','NCL','.nc'),
 ('PF','French Polynesia','Papeete','XPF','Franc','+689','PYF','.pf'),
 ('YT','Mayotte','Mamoudzou','EUR','Euro','+262','MYT','.yt'),
 ('GP','Saint Barthelemy','Gustavia','EUR','Euro','+590','GLP','.gp'),
 ('PM','Saint Pierre and Miquelon','Saint-Pierre','EUR','Euro','+508','SPM','.pm'),
 ('WF','Wallis and Futuna','Mata''utu','XPF','Franc','+681','WLF','.wf'),
 ('TF','French Southern and Antarctic Lands','Martin-de-Vivi�s','','','','ATF','.tf'),
 ('BV','Bouvet Island','','','','','BVT','.bv'),
 ('CK','Cook Islands','Avarua','NZD','Dollar','+682','COK','.ck'),
 ('NU','Niue','Alofi','NZD','Dollar','+683','NIU','.nu'),
 ('TK','Tokelau','','NZD','Dollar','+690','TKL','.tk'),
 ('GG','Guernsey','Saint Peter Port','GGP','Pound','+44','GGY','.gg'),
 ('IM','Isle of Man','Douglas','IMP','Pound','+44','IMN','.im'),
 ('JE','Jersey','Saint Helier','JEP','Pound','+44','JEY','.je'),
 ('AI','Anguilla','The Valley','XCD','Dollar','+1-264','AIA','.ai'),
 ('BM','Bermuda','Hamilton','BMD','Dollar','+1-441','BMU','.bm'),
 ('IO','British Indian Ocean Territory','','','','+246','IOT','.io'),
 ('VG','British Virgin Islands','Road Town','USD','Dollar','+1-284','VGB','.vg'),
 ('KY','Cayman Islands','George Town','KYD','Dollar','+1-345','CYM','.ky'),
 ('FK','Falkland Islands (Islas Malvinas)','Stanley','FKP','Pound','+500','FLK','.fk'),
 ('GI','Gibraltar','Gibraltar','GIP','Pound','+350','GIB','.gi'),
 ('MS','Montserrat','Plymouth','XCD','Dollar','+1-664','MSR','.ms'),
 ('PN','Pitcairn Islands','Adamstown','NZD','Dollar','','PCN','.pn'),
 ('SH','Saint Helena','Jamestown','SHP','Pound','+290','SHN','.sh'),
 ('GS','South Georgia and the South Sandwich Islands','','','','','SGS','.gs'),
 ('TC','Turks and Caicos Islands','Grand Turk','USD','Dollar','+1-649','TCA','.tc'),
 ('MP','Northern Mariana Islands','Saipan','USD','Dollar','+1-670','MNP','.mp'),
 ('PR','Puerto Rico','San Juan','USD','Dollar','+1-787','PRI','.pr'),
 ('AS','American Samoa','Pago Pago','USD','Dollar','+1-684','ASM','.as'),
 ('UM','Baker Island','','','','','UMI',''),
 ('GU','Guam','Hagatna','USD','Dollar','+1-671','GUM','.gu'),
 ('VI','U.S. Virgin Islands','Charlotte Amalie','USD','Dollar','+1-340','VIR','.vi'),
 ('HK','Hong Kong','','HKD','Dollar','+852','HKG','.hk'),
 ('MO','Macau','Macau','MOP','Pataca','+853','MAC','.mo'),
 ('FO','Faroe Islands','Torshavn','DKK','Krone','+298','FRO','.fo'),
 ('GL','Greenland','Nuuk (Godthab)','DKK','Krone','+299','GRL','.gl'),
 ('GF','French Guiana','Cayenne','EUR','Euro','+594','GUF','.gf'),
 ('MQ','Martinique','Fort-de-France','EUR','Euro','+596','MTQ','.mq'),
 ('RE','Reunion','Saint-Denis','EUR','Euro','+262','REU','.re'),
 ('AX','Aland','Mariehamn','EUR','Euro','+358-18','ALA','.ax'),
 ('AW','Aruba','Oranjestad','AWG','Guilder','+297','ABW','.aw'),
 ('AN','Netherlands Antilles','Willemstad','ANG','Guilder','+599','ANT','.an'),
 ('SJ','Svalbard','Longyearbyen','NOK','Krone','+47','SJM','.sj'),
 ('AC','Ascension','Georgetown','SHP','Pound','+247','ASC','.ac'),
 ('TA','Tristan da Cunha','Edinburgh','SHP','Pound','+290','TAA',''),
 ('AQ','Antarctica','','','','','ATA','.aq'),
 ('PS','Palestinian Territories (Gaza Strip and West Bank)','Gaza City (Gaza Strip) and Ramallah (West Bank)','ILS','Shekel','+970','PSE','.ps'),
 ('EH','Western Sahara','El-Aaiun','MAD','Dirham','+212','ESH','.eh')
on conflict do nothing;
insert into base.ent (ent_name,ent_type,username,country) values ('Admin','r','admin','US')
on conflict do nothing;
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values
 ('aar'  , 'aar'  , 'aa'  , 'Afar'  , 'afar'),
 ('abk'  , 'abk'  , 'ab'  , 'Abkhazian'  , 'abkhaze'),
 ('ace'  , 'ace'  , null  , 'Achinese'  , 'aceh'),
 ('ach'  , 'ach'  , null  , 'Acoli'  , 'acoli'),
 ('ada'  , 'ada'  , null  , 'Adangme'  , 'adangme'),
 ('ady'  , 'ady'  , null  , 'Adyghe; Adygei'  , 'adyghé'),
 ('afa'  , 'afa'  , null  , 'Afro-Asiatic languages'  , 'afro-asiatiques, langues'),
 ('afh'  , 'afh'  , null  , 'Afrihili'  , 'afrihili'),
 ('afr'  , 'afr'  , 'af'  , 'Afrikaans'  , 'afrikaans'),
 ('ain'  , 'ain'  , null  , 'Ainu'  , 'aïnou'),
 ('aka'  , 'aka'  , 'ak'  , 'Akan'  , 'akan'),
 ('akk'  , 'akk'  , null  , 'Akkadian'  , 'akkadien'),
 ('sqi'  , 'alb'  , 'sq'  , 'Albanian'  , 'albanais'),
 ('ale'  , 'ale'  , null  , 'Aleut'  , 'aléoute'),
 ('alg'  , 'alg'  , null  , 'Algonquian languages'  , 'algonquines, langues'),
 ('alt'  , 'alt'  , null  , 'Southern Altai'  , 'altai du Sud'),
 ('amh'  , 'amh'  , 'am'  , 'Amharic'  , 'amharique'),
 ('ang'  , 'ang'  , null  , 'English, Old (ca.450-1100)'  , 'anglo-saxon (ca.450-1100)'),
 ('anp'  , 'anp'  , null  , 'Angika'  , 'angika'),
 ('apa'  , 'apa'  , null  , 'Apache languages'  , 'apaches, langues'),
 ('ara'  , 'ara'  , 'ar'  , 'Arabic'  , 'arabe'),
 ('arc'  , 'arc'  , null  , 'Official Aramaic (700-300 BCE); Imperial Aramaic (700-300 BCE)'  , 'araméen d''empire (700-300 BCE)'),
 ('arg'  , 'arg'  , 'an'  , 'Aragonese'  , 'aragonais'),
 ('hye'  , 'arm'  , 'hy'  , 'Armenian'  , 'arménien'),
 ('arn'  , 'arn'  , null  , 'Mapudungun; Mapuche'  , 'mapudungun; mapuche; mapuce'),
 ('arp'  , 'arp'  , null  , 'Arapaho'  , 'arapaho'),
 ('art'  , 'art'  , null  , 'Artificial languages'  , 'artificielles, langues'),
 ('arw'  , 'arw'  , null  , 'Arawak'  , 'arawak'),
 ('asm'  , 'asm'  , 'as'  , 'Assamese'  , 'assamais'),
 ('ast'  , 'ast'  , null  , 'Asturian; Bable; Leonese; Asturleonese'  , 'asturien; bable; léonais; asturoléonais'),
 ('ath'  , 'ath'  , null  , 'Athapascan languages'  , 'athapascanes, langues'),
 ('aus'  , 'aus'  , null  , 'Australian languages'  , 'australiennes, langues'),
 ('ava'  , 'ava'  , 'av'  , 'Avaric'  , 'avar'),
 ('ave'  , 'ave'  , 'ae'  , 'Avestan'  , 'avestique'),
 ('awa'  , 'awa'  , null  , 'Awadhi'  , 'awadhi'),
 ('aym'  , 'aym'  , 'ay'  , 'Aymara'  , 'aymara'),
 ('aze'  , 'aze'  , 'az'  , 'Azerbaijani'  , 'azéri'),
 ('bad'  , 'bad'  , null  , 'Banda languages'  , 'banda, langues'),
 ('bai'  , 'bai'  , null  , 'Bamileke languages'  , 'bamiléké, langues'),
 ('bak'  , 'bak'  , 'ba'  , 'Bashkir'  , 'bachkir'),
 ('bal'  , 'bal'  , null  , 'Baluchi'  , 'baloutchi'),
 ('bam'  , 'bam'  , 'bm'  , 'Bambara'  , 'bambara'),
 ('ban'  , 'ban'  , null  , 'Balinese'  , 'balinais'),
 ('eus'  , 'baq'  , 'eu'  , 'Basque'  , 'basque'),
 ('bas'  , 'bas'  , null  , 'Basa'  , 'basa'),
 ('bat'  , 'bat'  , null  , 'Baltic languages'  , 'baltes, langues'),
 ('bej'  , 'bej'  , null  , 'Beja; Bedawiyet'  , 'bedja'),
 ('bel'  , 'bel'  , 'be'  , 'Belarusian'  , 'biélorusse'),
 ('bem'  , 'bem'  , null  , 'Bemba'  , 'bemba'),
 ('ben'  , 'ben'  , 'bn'  , 'Bengali'  , 'bengali'),
 ('ber'  , 'ber'  , null  , 'Berber languages'  , 'berbères, langues'),
 ('bho'  , 'bho'  , null  , 'Bhojpuri'  , 'bhojpuri'),
 ('bih'  , 'bih'  , 'bh'  , 'Bihari languages'  , 'langues biharis'),
 ('bik'  , 'bik'  , null  , 'Bikol'  , 'bikol'),
 ('bin'  , 'bin'  , null  , 'Bini; Edo'  , 'bini; edo'),
 ('bis'  , 'bis'  , 'bi'  , 'Bislama'  , 'bichlamar'),
 ('bla'  , 'bla'  , null  , 'Siksika'  , 'blackfoot'),
 ('bnt'  , 'bnt'  , null  , 'Bantu (Other)'  , 'bantoues, autres langues'),
 ('bos'  , 'bos'  , 'bs'  , 'Bosnian'  , 'bosniaque'),
 ('bra'  , 'bra'  , null  , 'Braj'  , 'braj'),
 ('bre'  , 'bre'  , 'br'  , 'Breton'  , 'breton'),
 ('btk'  , 'btk'  , null  , 'Batak languages'  , 'batak, langues'),
 ('bua'  , 'bua'  , null  , 'Buriat'  , 'bouriate'),
 ('bug'  , 'bug'  , null  , 'Buginese'  , 'bugi'),
 ('bul'  , 'bul'  , 'bg'  , 'Bulgarian'  , 'bulgare'),
 ('mya'  , 'bur'  , 'my'  , 'Burmese'  , 'birman'),
 ('byn'  , 'byn'  , null  , 'Blin; Bilin'  , 'blin; bilen'),
 ('cad'  , 'cad'  , null  , 'Caddo'  , 'caddo'),
 ('cai'  , 'cai'  , null  , 'Central American Indian languages'  , 'amérindiennes de L''Amérique centrale, langues'),
 ('car'  , 'car'  , null  , 'Galibi Carib'  , 'karib; galibi; carib'),
 ('cat'  , 'cat'  , 'ca'  , 'Catalan; Valencian'  , 'catalan; valencien'),
 ('cau'  , 'cau'  , null  , 'Caucasian languages'  , 'caucasiennes, langues'),
 ('ceb'  , 'ceb'  , null  , 'Cebuano'  , 'cebuano'),
 ('cel'  , 'cel'  , null  , 'Celtic languages'  , 'celtiques, langues; celtes, langues'),
 ('cha'  , 'cha'  , 'ch'  , 'Chamorro'  , 'chamorro'),
 ('chb'  , 'chb'  , null  , 'Chibcha'  , 'chibcha'),
 ('che'  , 'che'  , 'ce'  , 'Chechen'  , 'tchétchène'),
 ('chg'  , 'chg'  , null  , 'Chagatai'  , 'djaghataï'),
 ('zho'  , 'chi'  , 'zh'  , 'Chinese'  , 'chinois'),
 ('chk'  , 'chk'  , null  , 'Chuukese'  , 'chuuk'),
 ('chm'  , 'chm'  , null  , 'Mari'  , 'mari'),
 ('chn'  , 'chn'  , null  , 'Chinook jargon'  , 'chinook, jargon'),
 ('cho'  , 'cho'  , null  , 'Choctaw'  , 'choctaw'),
 ('chp'  , 'chp'  , null  , 'Chipewyan; Dene Suline'  , 'chipewyan'),
 ('chr'  , 'chr'  , null  , 'Cherokee'  , 'cherokee'),
 ('chu'  , 'chu'  , 'cu'  , 'Church Slavic; Old Slavonic; Church Slavonic; Old Bulgarian; Old Church Slavonic'  , 'slavon d''église; vieux slave; slavon liturgique; vieux bulgare'),
 ('chv'  , 'chv'  , 'cv'  , 'Chuvash'  , 'tchouvache'),
 ('chy'  , 'chy'  , null  , 'Cheyenne'  , 'cheyenne'),
 ('cmc'  , 'cmc'  , null  , 'Chamic languages'  , 'chames, langues'),
 ('cnr'  , 'cnr'  , null  , 'Montenegrin'  , 'monténégrin'),
 ('cop'  , 'cop'  , null  , 'Coptic'  , 'copte'),
 ('cor'  , 'cor'  , 'kw'  , 'Cornish'  , 'cornique'),
 ('cos'  , 'cos'  , 'co'  , 'Corsican'  , 'corse'),
 ('cpe'  , 'cpe'  , null  , 'Creoles and pidgins, English based'  , 'créoles et pidgins basés sur l''anglais'),
 ('cpf'  , 'cpf'  , null  , 'Creoles and pidgins, French-based'  , 'créoles et pidgins basés sur le français'),
 ('cpp'  , 'cpp'  , null  , 'Creoles and pidgins, Portuguese-based'  , 'créoles et pidgins basés sur le portugais'),
 ('cre'  , 'cre'  , 'cr'  , 'Cree'  , 'cree'),
 ('crh'  , 'crh'  , null  , 'Crimean Tatar; Crimean Turkish'  , 'tatar de Crimé'),
 ('crp'  , 'crp'  , null  , 'Creoles and pidgins'  , 'créoles et pidgins'),
 ('csb'  , 'csb'  , null  , 'Kashubian'  , 'kachoube'),
 ('cus'  , 'cus'  , null  , 'Cushitic languages'  , 'couchitiques, langues'),
 ('ces'  , 'cze'  , 'cs'  , 'Czech'  , 'tchèque'),
 ('dak'  , 'dak'  , null  , 'Dakota'  , 'dakota'),
 ('dan'  , 'dan'  , 'da'  , 'Danish'  , 'danois'),
 ('dar'  , 'dar'  , null  , 'Dargwa'  , 'dargwa'),
 ('day'  , 'day'  , null  , 'Land Dayak languages'  , 'dayak, langues'),
 ('del'  , 'del'  , null  , 'Delaware'  , 'delaware'),
 ('den'  , 'den'  , null  , 'Slave (Athapascan)'  , 'esclave (athapascan)'),
 ('dgr'  , 'dgr'  , null  , 'Dogrib'  , 'dogrib'),
 ('din'  , 'din'  , null  , 'Dinka'  , 'dinka'),
 ('div'  , 'div'  , 'dv'  , 'Divehi; Dhivehi; Maldivian'  , 'maldivien'),
 ('doi'  , 'doi'  , null  , 'Dogri'  , 'dogri'),
 ('dra'  , 'dra'  , null  , 'Dravidian languages'  , 'dravidiennes, langues'),
 ('dsb'  , 'dsb'  , null  , 'Lower Sorbian'  , 'bas-sorabe'),
 ('dua'  , 'dua'  , null  , 'Duala'  , 'douala'),
 ('dum'  , 'dum'  , null  , 'Dutch, Middle (ca.1050-1350)'  , 'néerlandais moyen (ca. 1050-1350)'),
 ('nld'  , 'dut'  , 'nl'  , 'Dutch; Flemish'  , 'néerlandais; flamand'),
 ('dyu'  , 'dyu'  , null  , 'Dyula'  , 'dioula'),
 ('dzo'  , 'dzo'  , 'dz'  , 'Dzongkha'  , 'dzongkha'),
 ('efi'  , 'efi'  , null  , 'Efik'  , 'efik'),
 ('egy'  , 'egy'  , null  , 'Egyptian (Ancient)'  , 'égyptien'),
 ('eka'  , 'eka'  , null  , 'Ekajuk'  , 'ekajuk'),
 ('elx'  , 'elx'  , null  , 'Elamite'  , 'élamite'),
 ('eng'  , 'eng'  , 'en'  , 'English'  , 'anglais'),
 ('enm'  , 'enm'  , null  , 'English, Middle (1100-1500)'  , 'anglais moyen (1100-1500)'),
 ('epo'  , 'epo'  , 'eo'  , 'Esperanto'  , 'espéranto'),
 ('est'  , 'est'  , 'et'  , 'Estonian'  , 'estonien'),
 ('ewe'  , 'ewe'  , 'ee'  , 'Ewe'  , 'éwé'),
 ('ewo'  , 'ewo'  , null  , 'Ewondo'  , 'éwondo'),
 ('fan'  , 'fan'  , null  , 'Fang'  , 'fang'),
 ('fao'  , 'fao'  , 'fo'  , 'Faroese'  , 'féroïen'),
 ('fat'  , 'fat'  , null  , 'Fanti'  , 'fanti'),
 ('fij'  , 'fij'  , 'fj'  , 'Fijian'  , 'fidjien'),
 ('fil'  , 'fil'  , null  , 'Filipino; Pilipino'  , 'filipino; pilipino'),
 ('fin'  , 'fin'  , 'fi'  , 'Finnish'  , 'finnois'),
 ('fiu'  , 'fiu'  , null  , 'Finno-Ugrian languages'  , 'finno-ougriennes, langues'),
 ('fon'  , 'fon'  , null  , 'Fon'  , 'fon'),
 ('fra'  , 'fre'  , 'fr'  , 'French'  , 'français'),
 ('frm'  , 'frm'  , null  , 'French, Middle (ca.1400-1600)'  , 'français moyen (1400-1600)'),
 ('fro'  , 'fro'  , null  , 'French, Old (842-ca.1400)'  , 'français ancien (842-ca.1400)'),
 ('frr'  , 'frr'  , null  , 'Northern Frisian'  , 'frison septentrional'),
 ('frs'  , 'frs'  , null  , 'Eastern Frisian'  , 'frison oriental'),
 ('fry'  , 'fry'  , 'fy'  , 'Western Frisian'  , 'frison occidental'),
 ('ful'  , 'ful'  , 'ff'  , 'Fulah'  , 'peul'),
 ('fur'  , 'fur'  , null  , 'Friulian'  , 'frioulan'),
 ('gaa'  , 'gaa'  , null  , 'Ga'  , 'ga'),
 ('gay'  , 'gay'  , null  , 'Gayo'  , 'gayo'),
 ('gba'  , 'gba'  , null  , 'Gbaya'  , 'gbaya'),
 ('gem'  , 'gem'  , null  , 'Germanic languages'  , 'germaniques, langues'),
 ('kat'  , 'geo'  , 'ka'  , 'Georgian'  , 'géorgien'),
 ('deu'  , 'ger'  , 'de'  , 'German'  , 'allemand'),
 ('gez'  , 'gez'  , null  , 'Geez'  , 'guèze'),
 ('gil'  , 'gil'  , null  , 'Gilbertese'  , 'kiribati'),
 ('gla'  , 'gla'  , 'gd'  , 'Gaelic; Scottish Gaelic'  , 'gaélique; gaélique écossais'),
 ('gle'  , 'gle'  , 'ga'  , 'Irish'  , 'irlandais'),
 ('glg'  , 'glg'  , 'gl'  , 'Galician'  , 'galicien'),
 ('glv'  , 'glv'  , 'gv'  , 'Manx'  , 'manx; mannois'),
 ('gmh'  , 'gmh'  , null  , 'German, Middle High (ca.1050-1500)'  , 'allemand, moyen haut (ca. 1050-1500)'),
 ('goh'  , 'goh'  , null  , 'German, Old High (ca.750-1050)'  , 'allemand, vieux haut (ca. 750-1050)'),
 ('gon'  , 'gon'  , null  , 'Gondi'  , 'gond'),
 ('gor'  , 'gor'  , null  , 'Gorontalo'  , 'gorontalo'),
 ('got'  , 'got'  , null  , 'Gothic'  , 'gothique'),
 ('grb'  , 'grb'  , null  , 'Grebo'  , 'grebo'),
 ('grc'  , 'grc'  , null  , 'Greek, Ancient (to 1453)'  , 'grec ancien (jusqu''à 1453)'),
 ('ell'  , 'gre'  , 'el'  , 'Greek, Modern (1453-)'  , 'grec moderne (après 1453)'),
 ('grn'  , 'grn'  , 'gn'  , 'Guarani'  , 'guarani'),
 ('gsw'  , 'gsw'  , null  , 'Swiss German; Alemannic; Alsatian'  , 'suisse alémanique; alémanique; alsacien'),
 ('guj'  , 'guj'  , 'gu'  , 'Gujarati'  , 'goudjrati'),
 ('gwi'  , 'gwi'  , null  , 'Gwich''in'  , 'gwich''in'),
 ('hai'  , 'hai'  , null  , 'Haida'  , 'haida'),
 ('hat'  , 'hat'  , 'ht'  , 'Haitian; Haitian Creole'  , 'haïtien; créole haïtien'),
 ('hau'  , 'hau'  , 'ha'  , 'Hausa'  , 'haoussa'),
 ('haw'  , 'haw'  , null  , 'Hawaiian'  , 'hawaïen'),
 ('heb'  , 'heb'  , 'he'  , 'Hebrew'  , 'hébreu'),
 ('her'  , 'her'  , 'hz'  , 'Herero'  , 'herero'),
 ('hil'  , 'hil'  , null  , 'Hiligaynon'  , 'hiligaynon'),
 ('him'  , 'him'  , null  , 'Himachali languages; Western Pahari languages'  , 'langues himachalis; langues paharis occidentales'),
 ('hin'  , 'hin'  , 'hi'  , 'Hindi'  , 'hindi'),
 ('hit'  , 'hit'  , null  , 'Hittite'  , 'hittite'),
 ('hmn'  , 'hmn'  , null  , 'Hmong; Mong'  , 'hmong'),
 ('hmo'  , 'hmo'  , 'ho'  , 'Hiri Motu'  , 'hiri motu'),
 ('hrv'  , 'hrv'  , 'hr'  , 'Croatian'  , 'croate'),
 ('hsb'  , 'hsb'  , null  , 'Upper Sorbian'  , 'haut-sorabe'),
 ('hun'  , 'hun'  , 'hu'  , 'Hungarian'  , 'hongrois'),
 ('hup'  , 'hup'  , null  , 'Hupa'  , 'hupa'),
 ('iba'  , 'iba'  , null  , 'Iban'  , 'iban'),
 ('ibo'  , 'ibo'  , 'ig'  , 'Igbo'  , 'igbo'),
 ('isl'  , 'ice'  , 'is'  , 'Icelandic'  , 'islandais'),
 ('ido'  , 'ido'  , 'io'  , 'Ido'  , 'ido'),
 ('iii'  , 'iii'  , 'ii'  , 'Sichuan Yi; Nuosu'  , 'yi de Sichuan'),
 ('ijo'  , 'ijo'  , null  , 'Ijo languages'  , 'ijo, langues'),
 ('iku'  , 'iku'  , 'iu'  , 'Inuktitut'  , 'inuktitut'),
 ('ile'  , 'ile'  , 'ie'  , 'Interlingue; Occidental'  , 'interlingue'),
 ('ilo'  , 'ilo'  , null  , 'Iloko'  , 'ilocano'),
 ('ina'  , 'ina'  , 'ia'  , 'Interlingua (International Auxiliary Language Association)'  , 'interlingua (langue auxiliaire internationale)'),
 ('inc'  , 'inc'  , null  , 'Indic languages'  , 'indo-aryennes, langues'),
 ('ind'  , 'ind'  , 'id'  , 'Indonesian'  , 'indonésien'),
 ('ine'  , 'ine'  , null  , 'Indo-European languages'  , 'indo-européennes, langues'),
 ('inh'  , 'inh'  , null  , 'Ingush'  , 'ingouche'),
 ('ipk'  , 'ipk'  , 'ik'  , 'Inupiaq'  , 'inupiaq'),
 ('ira'  , 'ira'  , null  , 'Iranian languages'  , 'iraniennes, langues'),
 ('iro'  , 'iro'  , null  , 'Iroquoian languages'  , 'iroquoises, langues'),
 ('ita'  , 'ita'  , 'it'  , 'Italian'  , 'italien'),
 ('jav'  , 'jav'  , 'jv'  , 'Javanese'  , 'javanais'),
 ('jbo'  , 'jbo'  , null  , 'Lojban'  , 'lojban'),
 ('jpn'  , 'jpn'  , 'ja'  , 'Japanese'  , 'japonais'),
 ('jpr'  , 'jpr'  , null  , 'Judeo-Persian'  , 'judéo-persan'),
 ('jrb'  , 'jrb'  , null  , 'Judeo-Arabic'  , 'judéo-arabe'),
 ('kaa'  , 'kaa'  , null  , 'Kara-Kalpak'  , 'karakalpak'),
 ('kab'  , 'kab'  , null  , 'Kabyle'  , 'kabyle'),
 ('kac'  , 'kac'  , null  , 'Kachin; Jingpho'  , 'kachin; jingpho'),
 ('kal'  , 'kal'  , 'kl'  , 'Kalaallisut; Greenlandic'  , 'groenlandais'),
 ('kam'  , 'kam'  , null  , 'Kamba'  , 'kamba'),
 ('kan'  , 'kan'  , 'kn'  , 'Kannada'  , 'kannada'),
 ('kar'  , 'kar'  , null  , 'Karen languages'  , 'karen, langues'),
 ('kas'  , 'kas'  , 'ks'  , 'Kashmiri'  , 'kashmiri'),
 ('kau'  , 'kau'  , 'kr'  , 'Kanuri'  , 'kanouri'),
 ('kaw'  , 'kaw'  , null  , 'Kawi'  , 'kawi'),
 ('kaz'  , 'kaz'  , 'kk'  , 'Kazakh'  , 'kazakh'),
 ('kbd'  , 'kbd'  , null  , 'Kabardian'  , 'kabardien'),
 ('kha'  , 'kha'  , null  , 'Khasi'  , 'khasi'),
 ('khi'  , 'khi'  , null  , 'Khoisan languages'  , 'khoïsan, langues'),
 ('khm'  , 'khm'  , 'km'  , 'Central Khmer'  , 'khmer central'),
 ('kho'  , 'kho'  , null  , 'Khotanese; Sakan'  , 'khotanais; sakan'),
 ('kik'  , 'kik'  , 'ki'  , 'Kikuyu; Gikuyu'  , 'kikuyu'),
 ('kin'  , 'kin'  , 'rw'  , 'Kinyarwanda'  , 'rwanda'),
 ('kir'  , 'kir'  , 'ky'  , 'Kirghiz; Kyrgyz'  , 'kirghiz'),
 ('kmb'  , 'kmb'  , null  , 'Kimbundu'  , 'kimbundu'),
 ('kok'  , 'kok'  , null  , 'Konkani'  , 'konkani'),
 ('kom'  , 'kom'  , 'kv'  , 'Komi'  , 'kom'),
 ('kon'  , 'kon'  , 'kg'  , 'Kongo'  , 'kongo'),
 ('kor'  , 'kor'  , 'ko'  , 'Korean'  , 'coréen'),
 ('kos'  , 'kos'  , null  , 'Kosraean'  , 'kosrae'),
 ('kpe'  , 'kpe'  , null  , 'Kpelle'  , 'kpellé'),
 ('krc'  , 'krc'  , null  , 'Karachay-Balkar'  , 'karatchai balkar'),
 ('krl'  , 'krl'  , null  , 'Karelian'  , 'carélien'),
 ('kro'  , 'kro'  , null  , 'Kru languages'  , 'krou, langues'),
 ('kru'  , 'kru'  , null  , 'Kurukh'  , 'kurukh'),
 ('kua'  , 'kua'  , 'kj'  , 'Kuanyama; Kwanyama'  , 'kuanyama; kwanyama'),
 ('kum'  , 'kum'  , null  , 'Kumyk'  , 'koumyk'),
 ('kur'  , 'kur'  , 'ku'  , 'Kurdish'  , 'kurde'),
 ('kut'  , 'kut'  , null  , 'Kutenai'  , 'kutenai'),
 ('lad'  , 'lad'  , null  , 'Ladino'  , 'judéo-espagnol'),
 ('lah'  , 'lah'  , null  , 'Lahnda'  , 'lahnda'),
 ('lam'  , 'lam'  , null  , 'Lamba'  , 'lamba'),
 ('lao'  , 'lao'  , 'lo'  , 'Lao'  , 'lao'),
 ('lat'  , 'lat'  , 'la'  , 'Latin'  , 'latin'),
 ('lav'  , 'lav'  , 'lv'  , 'Latvian'  , 'letton'),
 ('lez'  , 'lez'  , null  , 'Lezghian'  , 'lezghien'),
 ('lim'  , 'lim'  , 'li'  , 'Limburgan; Limburger; Limburgish'  , 'limbourgeois'),
 ('lin'  , 'lin'  , 'ln'  , 'Lingala'  , 'lingala'),
 ('lit'  , 'lit'  , 'lt'  , 'Lithuanian'  , 'lituanien'),
 ('lol'  , 'lol'  , null  , 'Mongo'  , 'mongo'),
 ('loz'  , 'loz'  , null  , 'Lozi'  , 'lozi'),
 ('ltz'  , 'ltz'  , 'lb'  , 'Luxembourgish; Letzeburgesch'  , 'luxembourgeois'),
 ('lua'  , 'lua'  , null  , 'Luba-Lulua'  , 'luba-lulua'),
 ('lub'  , 'lub'  , 'lu'  , 'Luba-Katanga'  , 'luba-katanga'),
 ('lug'  , 'lug'  , 'lg'  , 'Ganda'  , 'ganda'),
 ('lui'  , 'lui'  , null  , 'Luiseno'  , 'luiseno'),
 ('lun'  , 'lun'  , null  , 'Lunda'  , 'lunda'),
 ('luo'  , 'luo'  , null  , 'Luo (Kenya and Tanzania)'  , 'luo (Kenya et Tanzanie)'),
 ('lus'  , 'lus'  , null  , 'Lushai'  , 'lushai'),
 ('mkd'  , 'mac'  , 'mk'  , 'Macedonian'  , 'macédonien'),
 ('mad'  , 'mad'  , null  , 'Madurese'  , 'madourais'),
 ('mag'  , 'mag'  , null  , 'Magahi'  , 'magahi'),
 ('mah'  , 'mah'  , 'mh'  , 'Marshallese'  , 'marshall'),
 ('mai'  , 'mai'  , null  , 'Maithili'  , 'maithili'),
 ('mak'  , 'mak'  , null  , 'Makasar'  , 'makassar'),
 ('mal'  , 'mal'  , 'ml'  , 'Malayalam'  , 'malayalam'),
 ('man'  , 'man'  , null  , 'Mandingo'  , 'mandingue'),
 ('mri'  , 'mao'  , 'mi'  , 'Maori'  , 'maori'),
 ('map'  , 'map'  , null  , 'Austronesian languages'  , 'austronésiennes, langues'),
 ('mar'  , 'mar'  , 'mr'  , 'Marathi'  , 'marathe'),
 ('mas'  , 'mas'  , null  , 'Masai'  , 'massaï'),
 ('msa'  , 'may'  , 'ms'  , 'Malay'  , 'malais'),
 ('mdf'  , 'mdf'  , null  , 'Moksha'  , 'moksa'),
 ('mdr'  , 'mdr'  , null  , 'Mandar'  , 'mandar'),
 ('men'  , 'men'  , null  , 'Mende'  , 'mendé'),
 ('mga'  , 'mga'  , null  , 'Irish, Middle (900-1200)'  , 'irlandais moyen (900-1200)'),
 ('mic'  , 'mic'  , null  , 'Mi''kmaq; Micmac'  , 'mi''kmaq; micmac'),
 ('min'  , 'min'  , null  , 'Minangkabau'  , 'minangkabau'),
 ('mis'  , 'mis'  , null  , 'Uncoded languages'  , 'langues non codées'),
 ('mkh'  , 'mkh'  , null  , 'Mon-Khmer languages'  , 'môn-khmer, langues'),
 ('mlg'  , 'mlg'  , 'mg'  , 'Malagasy'  , 'malgache'),
 ('mlt'  , 'mlt'  , 'mt'  , 'Maltese'  , 'maltais'),
 ('mnc'  , 'mnc'  , null  , 'Manchu'  , 'mandchou'),
 ('mni'  , 'mni'  , null  , 'Manipuri'  , 'manipuri'),
 ('mno'  , 'mno'  , null  , 'Manobo languages'  , 'manobo, langues'),
 ('moh'  , 'moh'  , null  , 'Mohawk'  , 'mohawk'),
 ('mon'  , 'mon'  , 'mn'  , 'Mongolian'  , 'mongol'),
 ('mos'  , 'mos'  , null  , 'Mossi'  , 'moré'),
 ('mul'  , 'mul'  , null  , 'Multiple languages'  , 'multilingue'),
 ('mun'  , 'mun'  , null  , 'Munda languages'  , 'mounda, langues'),
 ('mus'  , 'mus'  , null  , 'Creek'  , 'muskogee'),
 ('mwl'  , 'mwl'  , null  , 'Mirandese'  , 'mirandais'),
 ('mwr'  , 'mwr'  , null  , 'Marwari'  , 'marvari'),
 ('myn'  , 'myn'  , null  , 'Mayan languages'  , 'maya, langues'),
 ('myv'  , 'myv'  , null  , 'Erzya'  , 'erza'),
 ('nah'  , 'nah'  , null  , 'Nahuatl languages'  , 'nahuatl, langues'),
 ('nai'  , 'nai'  , null  , 'North American Indian languages'  , 'nord-amérindiennes, langues'),
 ('nap'  , 'nap'  , null  , 'Neapolitan'  , 'napolitain'),
 ('nau'  , 'nau'  , 'na'  , 'Nauru'  , 'nauruan'),
 ('nav'  , 'nav'  , 'nv'  , 'Navajo; Navaho'  , 'navaho'),
 ('nbl'  , 'nbl'  , 'nr'  , 'Ndebele, South; South Ndebele'  , 'ndébélé du Sud'),
 ('nde'  , 'nde'  , 'nd'  , 'Ndebele, North; North Ndebele'  , 'ndébélé du Nord'),
 ('ndo'  , 'ndo'  , 'ng'  , 'Ndonga'  , 'ndonga'),
 ('nds'  , 'nds'  , null  , 'Low German; Low Saxon; German, Low; Saxon, Low'  , 'bas allemand; bas saxon; allemand, bas; saxon, bas'),
 ('nep'  , 'nep'  , 'ne'  , 'Nepali'  , 'népalais'),
 ('new'  , 'new'  , null  , 'Nepal Bhasa; Newari'  , 'nepal bhasa; newari'),
 ('nia'  , 'nia'  , null  , 'Nias'  , 'nias'),
 ('nic'  , 'nic'  , null  , 'Niger-Kordofanian languages'  , 'nigéro-kordofaniennes, langues'),
 ('niu'  , 'niu'  , null  , 'Niuean'  , 'niué'),
 ('nno'  , 'nno'  , 'nn'  , 'Norwegian Nynorsk; Nynorsk, Norwegian'  , 'norvégien nynorsk; nynorsk, norvégien'),
 ('nob'  , 'nob'  , 'nb'  , 'Bokmål, Norwegian; Norwegian Bokmål'  , 'norvégien bokmål'),
 ('nog'  , 'nog'  , null  , 'Nogai'  , 'nogaï; nogay'),
 ('non'  , 'non'  , null  , 'Norse, Old'  , 'norrois, vieux'),
 ('nor'  , 'nor'  , 'no'  , 'Norwegian'  , 'norvégien'),
 ('nqo'  , 'nqo'  , null  , 'N''Ko'  , 'n''ko'),
 ('nso'  , 'nso'  , null  , 'Pedi; Sepedi; Northern Sotho'  , 'pedi; sepedi; sotho du Nord'),
 ('nub'  , 'nub'  , null  , 'Nubian languages'  , 'nubiennes, langues'),
 ('nwc'  , 'nwc'  , null  , 'Classical Newari; Old Newari; Classical Nepal Bhasa'  , 'newari classique'),
 ('nya'  , 'nya'  , 'ny'  , 'Chichewa; Chewa; Nyanja'  , 'chichewa; chewa; nyanja'),
 ('nym'  , 'nym'  , null  , 'Nyamwezi'  , 'nyamwezi'),
 ('nyn'  , 'nyn'  , null  , 'Nyankole'  , 'nyankolé'),
 ('nyo'  , 'nyo'  , null  , 'Nyoro'  , 'nyoro'),
 ('nzi'  , 'nzi'  , null  , 'Nzima'  , 'nzema'),
 ('oci'  , 'oci'  , 'oc'  , 'Occitan (post 1500); Provençal'  , 'occitan (après 1500); provençal'),
 ('oji'  , 'oji'  , 'oj'  , 'Ojibwa'  , 'ojibwa'),
 ('ori'  , 'ori'  , 'or'  , 'Oriya'  , 'oriya'),
 ('orm'  , 'orm'  , 'om'  , 'Oromo'  , 'galla'),
 ('osa'  , 'osa'  , null  , 'Osage'  , 'osage'),
 ('oss'  , 'oss'  , 'os'  , 'Ossetian; Ossetic'  , 'ossète'),
 ('ota'  , 'ota'  , null  , 'Turkish, Ottoman (1500-1928)'  , 'turc ottoman (1500-1928)'),
 ('oto'  , 'oto'  , null  , 'Otomian languages'  , 'otomi, langues'),
 ('paa'  , 'paa'  , null  , 'Papuan languages'  , 'papoues, langues'),
 ('pag'  , 'pag'  , null  , 'Pangasinan'  , 'pangasinan'),
 ('pal'  , 'pal'  , null  , 'Pahlavi'  , 'pahlavi'),
 ('pam'  , 'pam'  , null  , 'Pampanga; Kapampangan'  , 'pampangan'),
 ('pan'  , 'pan'  , 'pa'  , 'Panjabi; Punjabi'  , 'pendjabi'),
 ('pap'  , 'pap'  , null  , 'Papiamento'  , 'papiamento'),
 ('pau'  , 'pau'  , null  , 'Palauan'  , 'palau'),
 ('peo'  , 'peo'  , null  , 'Persian, Old (ca.600-400 B.C.)'  , 'perse, vieux (ca. 600-400 av. J.-C.)'),
 ('fas'  , 'per'  , 'fa'  , 'Persian'  , 'persan'),
 ('phi'  , 'phi'  , null  , 'Philippine languages'  , 'philippines, langues'),
 ('phn'  , 'phn'  , null  , 'Phoenician'  , 'phénicien'),
 ('pli'  , 'pli'  , 'pi'  , 'Pali'  , 'pali'),
 ('pol'  , 'pol'  , 'pl'  , 'Polish'  , 'polonais'),
 ('pon'  , 'pon'  , null  , 'Pohnpeian'  , 'pohnpei'),
 ('por'  , 'por'  , 'pt'  , 'Portuguese'  , 'portugais'),
 ('pra'  , 'pra'  , null  , 'Prakrit languages'  , 'prâkrit, langues'),
 ('pro'  , 'pro'  , null  , 'Provençal, Old (to 1500)'  , 'provençal ancien (jusqu''à 1500)'),
 ('pus'  , 'pus'  , 'ps'  , 'Pushto; Pashto'  , 'pachto'),
 ('que'  , 'que'  , 'qu'  , 'Quechua'  , 'quechua'),
 ('raj'  , 'raj'  , null  , 'Rajasthani'  , 'rajasthani'),
 ('rap'  , 'rap'  , null  , 'Rapanui'  , 'rapanui'),
 ('rar'  , 'rar'  , null  , 'Rarotongan; Cook Islands Maori'  , 'rarotonga; maori des îles Cook'),
 ('roa'  , 'roa'  , null  , 'Romance languages'  , 'romanes, langues'),
 ('roh'  , 'roh'  , 'rm'  , 'Romansh'  , 'romanche'),
 ('rom'  , 'rom'  , null  , 'Romany'  , 'tsigane'),
 ('ron'  , 'rum'  , 'ro'  , 'Romanian; Moldavian; Moldovan'  , 'roumain; moldave'),
 ('run'  , 'run'  , 'rn'  , 'Rundi'  , 'rundi'),
 ('rup'  , 'rup'  , null  , 'Aromanian; Arumanian; Macedo-Romanian'  , 'aroumain; macédo-roumain'),
 ('rus'  , 'rus'  , 'ru'  , 'Russian'  , 'russe'),
 ('sad'  , 'sad'  , null  , 'Sandawe'  , 'sandawe'),
 ('sag'  , 'sag'  , 'sg'  , 'Sango'  , 'sango'),
 ('sah'  , 'sah'  , null  , 'Yakut'  , 'iakoute'),
 ('sai'  , 'sai'  , null  , 'South American Indian (Other)'  , 'indiennes d''Amérique du Sud, autres langues'),
 ('sal'  , 'sal'  , null  , 'Salishan languages'  , 'salishennes, langues'),
 ('sam'  , 'sam'  , null  , 'Samaritan Aramaic'  , 'samaritain'),
 ('san'  , 'san'  , 'sa'  , 'Sanskrit'  , 'sanskrit'),
 ('sas'  , 'sas'  , null  , 'Sasak'  , 'sasak'),
 ('sat'  , 'sat'  , null  , 'Santali'  , 'santal'),
 ('scn'  , 'scn'  , null  , 'Sicilian'  , 'sicilien'),
 ('sco'  , 'sco'  , null  , 'Scots'  , 'écossais'),
 ('sel'  , 'sel'  , null  , 'Selkup'  , 'selkoupe'),
 ('sem'  , 'sem'  , null  , 'Semitic languages'  , 'sémitiques, langues'),
 ('sga'  , 'sga'  , null  , 'Irish, Old (to 900)'  , 'irlandais ancien (jusqu''à 900)'),
 ('sgn'  , 'sgn'  , null  , 'Sign Languages'  , 'langues des signes'),
 ('shn'  , 'shn'  , null  , 'Shan'  , 'chan'),
 ('sid'  , 'sid'  , null  , 'Sidamo'  , 'sidamo'),
 ('sin'  , 'sin'  , 'si'  , 'Sinhala; Sinhalese'  , 'singhalais'),
 ('sio'  , 'sio'  , null  , 'Siouan languages'  , 'sioux, langues'),
 ('sit'  , 'sit'  , null  , 'Sino-Tibetan languages'  , 'sino-tibétaines, langues'),
 ('sla'  , 'sla'  , null  , 'Slavic languages'  , 'slaves, langues'),
 ('slk'  , 'slo'  , 'sk'  , 'Slovak'  , 'slovaque'),
 ('slv'  , 'slv'  , 'sl'  , 'Slovenian'  , 'slovène'),
 ('sma'  , 'sma'  , null  , 'Southern Sami'  , 'sami du Sud'),
 ('sme'  , 'sme'  , 'se'  , 'Northern Sami'  , 'sami du Nord'),
 ('smi'  , 'smi'  , null  , 'Sami languages'  , 'sames, langues'),
 ('smj'  , 'smj'  , null  , 'Lule Sami'  , 'sami de Lule'),
 ('smn'  , 'smn'  , null  , 'Inari Sami'  , 'sami d''Inari'),
 ('smo'  , 'smo'  , 'sm'  , 'Samoan'  , 'samoan'),
 ('sms'  , 'sms'  , null  , 'Skolt Sami'  , 'sami skolt'),
 ('sna'  , 'sna'  , 'sn'  , 'Shona'  , 'shona'),
 ('snd'  , 'snd'  , 'sd'  , 'Sindhi'  , 'sindhi'),
 ('snk'  , 'snk'  , null  , 'Soninke'  , 'soninké'),
 ('sog'  , 'sog'  , null  , 'Sogdian'  , 'sogdien'),
 ('som'  , 'som'  , 'so'  , 'Somali'  , 'somali'),
 ('son'  , 'son'  , null  , 'Songhai languages'  , 'songhai, langues'),
 ('sot'  , 'sot'  , 'st'  , 'Sotho, Southern'  , 'sotho du Sud'),
 ('spa'  , 'spa'  , 'es'  , 'Spanish; Castilian'  , 'espagnol; castillan'),
 ('srd'  , 'srd'  , 'sc'  , 'Sardinian'  , 'sarde'),
 ('srn'  , 'srn'  , null  , 'Sranan Tongo'  , 'sranan tongo'),
 ('srp'  , 'srp'  , 'sr'  , 'Serbian'  , 'serbe'),
 ('srr'  , 'srr'  , null  , 'Serer'  , 'sérère'),
 ('ssa'  , 'ssa'  , null  , 'Nilo-Saharan languages'  , 'nilo-sahariennes, langues'),
 ('ssw'  , 'ssw'  , 'ss'  , 'Swati'  , 'swati'),
 ('suk'  , 'suk'  , null  , 'Sukuma'  , 'sukuma'),
 ('sun'  , 'sun'  , 'su'  , 'Sundanese'  , 'soundanais'),
 ('sus'  , 'sus'  , null  , 'Susu'  , 'soussou'),
 ('sux'  , 'sux'  , null  , 'Sumerian'  , 'sumérien'),
 ('swa'  , 'swa'  , 'sw'  , 'Swahili'  , 'swahili'),
 ('swe'  , 'swe'  , 'sv'  , 'Swedish'  , 'suédois'),
 ('syc'  , 'syc'  , null  , 'Classical Syriac'  , 'syriaque classique'),
 ('syr'  , 'syr'  , null  , 'Syriac'  , 'syriaque'),
 ('tah'  , 'tah'  , 'ty'  , 'Tahitian'  , 'tahitien'),
 ('tai'  , 'tai'  , null  , 'Tai languages'  , 'tai, langues'),
 ('tam'  , 'tam'  , 'ta'  , 'Tamil'  , 'tamoul'),
 ('tat'  , 'tat'  , 'tt'  , 'Tatar'  , 'tatar'),
 ('tel'  , 'tel'  , 'te'  , 'Telugu'  , 'télougou'),
 ('tem'  , 'tem'  , null  , 'Timne'  , 'temne'),
 ('ter'  , 'ter'  , null  , 'Tereno'  , 'tereno'),
 ('tet'  , 'tet'  , null  , 'Tetum'  , 'tetum'),
 ('tgk'  , 'tgk'  , 'tg'  , 'Tajik'  , 'tadjik'),
 ('tgl'  , 'tgl'  , 'tl'  , 'Tagalog'  , 'tagalog'),
 ('tha'  , 'tha'  , 'th'  , 'Thai'  , 'thaï'),
 ('bod'  , 'tib'  , 'bo'  , 'Tibetan'  , 'tibétain'),
 ('tig'  , 'tig'  , null  , 'Tigre'  , 'tigré'),
 ('tir'  , 'tir'  , 'ti'  , 'Tigrinya'  , 'tigrigna'),
 ('tiv'  , 'tiv'  , null  , 'Tiv'  , 'tiv'),
 ('tkl'  , 'tkl'  , null  , 'Tokelau'  , 'tokelau'),
 ('tlh'  , 'tlh'  , null  , 'Klingon; tlhIngan-Hol'  , 'klingon'),
 ('tli'  , 'tli'  , null  , 'Tlingit'  , 'tlingit'),
 ('tmh'  , 'tmh'  , null  , 'Tamashek'  , 'tamacheq'),
 ('tog'  , 'tog'  , null  , 'Tonga (Nyasa)'  , 'tonga (Nyasa)'),
 ('ton'  , 'ton'  , 'to'  , 'Tonga (Tonga Islands)'  , 'tongan (Îles Tonga)'),
 ('tpi'  , 'tpi'  , null  , 'Tok Pisin'  , 'tok pisin'),
 ('tsi'  , 'tsi'  , null  , 'Tsimshian'  , 'tsimshian'),
 ('tsn'  , 'tsn'  , 'tn'  , 'Tswana'  , 'tswana'),
 ('tso'  , 'tso'  , 'ts'  , 'Tsonga'  , 'tsonga'),
 ('tuk'  , 'tuk'  , 'tk'  , 'Turkmen'  , 'turkmène'),
 ('tum'  , 'tum'  , null  , 'Tumbuka'  , 'tumbuka'),
 ('tup'  , 'tup'  , null  , 'Tupi languages'  , 'tupi, langues'),
 ('tur'  , 'tur'  , 'tr'  , 'Turkish'  , 'turc'),
 ('tut'  , 'tut'  , null  , 'Altaic languages'  , 'altaïques, langues'),
 ('tvl'  , 'tvl'  , null  , 'Tuvalu'  , 'tuvalu'),
 ('twi'  , 'twi'  , 'tw'  , 'Twi'  , 'twi'),
 ('tyv'  , 'tyv'  , null  , 'Tuvinian'  , 'touva'),
 ('udm'  , 'udm'  , null  , 'Udmurt'  , 'oudmourte'),
 ('uga'  , 'uga'  , null  , 'Ugaritic'  , 'ougaritique'),
 ('uig'  , 'uig'  , 'ug'  , 'Uighur; Uyghur'  , 'ouïgour'),
 ('ukr'  , 'ukr'  , 'uk'  , 'Ukrainian'  , 'ukrainien'),
 ('umb'  , 'umb'  , null  , 'Umbundu'  , 'umbundu'),
 ('und'  , 'und'  , null  , 'Undetermined'  , 'indéterminée'),
 ('urd'  , 'urd'  , 'ur'  , 'Urdu'  , 'ourdou'),
 ('uzb'  , 'uzb'  , 'uz'  , 'Uzbek'  , 'ouszbek'),
 ('vai'  , 'vai'  , null  , 'Vai'  , 'vaï'),
 ('ven'  , 'ven'  , 've'  , 'Venda'  , 'venda'),
 ('vie'  , 'vie'  , 'vi'  , 'Vietnamese'  , 'vietnamien'),
 ('vol'  , 'vol'  , 'vo'  , 'Volapük'  , 'volapük'),
 ('vot'  , 'vot'  , null  , 'Votic'  , 'vote'),
 ('wak'  , 'wak'  , null  , 'Wakashan languages'  , 'wakashanes, langues'),
 ('wal'  , 'wal'  , null  , 'Walamo'  , 'walamo'),
 ('war'  , 'war'  , null  , 'Waray'  , 'waray'),
 ('was'  , 'was'  , null  , 'Washo'  , 'washo'),
 ('cym'  , 'wel'  , 'cy'  , 'Welsh'  , 'gallois'),
 ('wen'  , 'wen'  , null  , 'Sorbian languages'  , 'sorabes, langues'),
 ('wln'  , 'wln'  , 'wa'  , 'Walloon'  , 'wallon'),
 ('wol'  , 'wol'  , 'wo'  , 'Wolof'  , 'wolof'),
 ('xal'  , 'xal'  , null  , 'Kalmyk; Oirat'  , 'kalmouk; oïrat'),
 ('xho'  , 'xho'  , 'xh'  , 'Xhosa'  , 'xhosa'),
 ('yao'  , 'yao'  , null  , 'Yao'  , 'yao'),
 ('yap'  , 'yap'  , null  , 'Yapese'  , 'yapois'),
 ('yid'  , 'yid'  , 'yi'  , 'Yiddish'  , 'yiddish'),
 ('yor'  , 'yor'  , 'yo'  , 'Yoruba'  , 'yoruba'),
 ('ypk'  , 'ypk'  , null  , 'Yupik languages'  , 'yupik, langues'),
 ('zap'  , 'zap'  , null  , 'Zapotec'  , 'zapotèque'),
 ('zbl'  , 'zbl'  , null  , 'Blissymbols; Blissymbolics; Bliss'  , 'symboles Bliss; Bliss'),
 ('zen'  , 'zen'  , null  , 'Zenaga'  , 'zenaga'),
 ('zgh'  , 'zgh'  , null  , 'Standard Moroccan Tamazight'  , 'amazighe standard marocain'),
 ('zha'  , 'zha'  , 'za'  , 'Zhuang; Chuang'  , 'zhuang; chuang'),
 ('znd'  , 'znd'  , null  , 'Zande languages'  , 'zandé, langues'),
 ('zul'  , 'zul'  , 'zu'  , 'Zulu'  , 'zoulou'),
 ('zun'  , 'zun'  , null  , 'Zuni'  , 'zuni'),
 ('zxx'  , 'zxx'  , null  , 'No linguistic content; Not applicable'  , 'pas de contenu linguistique; non applicable'),
 ('zza'  , 'zza'  , null  , 'Zaza; Dimili; Dimli; Kirdki; Kirmanjki; Zazaki'  , 'zaza; dimili; dimli; kirdki; kirmanjki; zazaki')
on conflict do nothing;
insert into base.parm (module, parm, type, v_int, v_text) values 
 ('wyseman', 'host', 'text', null, 'localhost'),
 ('wyseman', 'port', 'int', 54320, null)

on conflict do nothing;
select base.priv_grants();
insert into mychips.contracts (domain, name, version, language, published, digest, title, text, sections) values

(
      'mychips.org',
      'CHIP_Definition',
      1,
      'eng',
      '2020-04-01',
      E'\\x6a3fe8b8b275127c2f8168ea4a544916aa6173c73ca66e2d25bb5971b26ebdb6',
      'Defining a CHIP',
      'MyCHIPs is a standardized protocol to facilitate the documentation and exchange of Pledges of Credit between willing parties. This Credit is comprised of a number of individual promises, or Chits, made by one Party, for the benefit of the other Party, to deliver future value according to terms and conditions mutually agreed upon by the Parties. The party Pledging the future value is referred to as the Issuer. The party the Pledge is made to is referred to as the Recipient. A Pledge accrues as a receivable asset to the Recipient and a payable liability to the Issuer just as with any open-account indebtedness that might be incurred in the ordinary course of business.',
      '[{"text":"The amount of value represented in a Tally or a Chit is quantified in units of CHIPs. Internally a MyCHIPs server is expected to record transactions in integer units of 1/1000th of a CHIP. User interfaces are expected to render values as decimal CHIPs with up to 3 digits after a decimal point, for example: 1234.567."},{"text":"All transactions associated with this Tally shall be quantified exlusively in CHIPs, as defined herein, and not using any other unit of measure. For example, it is a breach of this covenant to produce a Pledge which the Parties understand to be measured in Dollars or Euros. It is not a breach to buy or sell Dollars, or any other currency, using this Tally and/or at a price denominated in CHIPs."},{"text":"One CHIP is defined as having a value equal to:","sections":[{"text":"The value produced by one continuously applied hour of adult human work;"},{"text":"in such circumstance where there is neither a shortage nor a surplus of such willing labor available; and"},{"text":"where the task can be reasonably understood with only minimal training and orientation; and"},{"text":"without considering the added productivity achieved by the use of labor-saving capital equipment; and"},{"text":"where the person performing the work has a normal, or average, functioning mind and body; and"},{"text":"can communicate effectively as needed with others in the work; and"},{"text":"can read and write effectively as needed to understand the work; and"},{"text":"understands, and can effectively employ basic arithmetic and counting as necessary for the work; and"},{"text":"otherwise, possesses no unusual strengths, weaknesses, developed skills, talents or abilities relevant to the work."}]}]'
    )
,(
      'mychips.org',
      'Credit_Terms',
      1,
      'eng',
      '2020-04-01',
      E'\\xc558ca3d0795343b073ca448db819fefdbd56a8ad4171363812a1d427b6a6d85',
      'Terms and Conditions for Credit Authorized by Stock and Foil',
      'When executing a Tally Agreement with each other, the Client and Vendor each decide the amount of credit they will extend to the other Party. They may also specify parameters that influence how and when the debt will be satisfied. Those parameters are referred to generally as Credit Terms. Such terms can be specified by the Vendor to be applied by credit issued by the Client. They can also be specified by the Client to be applied by credit issued by the Vendor in such cases where the Tally may develop a negative balance. The various credit terms are defined as follows:',
      '[{"title":"Maximum Balance","text":"This indicates the most the Issuer can count on borrowing against Product it obtains from the Recipient. The balance may be expressed as a single number, or as an expression, which is a function of time. Expressions may be used to amortize a loan, requiring principal to be paid down over time."},{"title":"Maximum Paydown","text":"This specifies the most the Issuer can pay down principal in advance of otherwise prevailing requirements and have his interest calculations reduced accordingly. This can be used to create a minimum interest return for a Recipient, while still allowing the Issuer to store value in the loan balance."},{"title":"Compound Interval","text":"The amount of time that passes before interest is calculated and applied to a balance. This may also define when payments are due. For example, if the application of such a charge raises a balance above the Maximum Balance, some kind of Lifting will have to occur to correct this."},{"title":"Grace Period","text":"New amounts of indebtedness will not accrue interest charges until this amount of time has passed."},{"title":"Rate","text":"An annualized rate expressed as a positive floating point number. For example, 0.05 means 5% per annum. This number will be scaled to match the Compound Interval in order to compute the interest/dividend charges to be applied during that an interval."},{"title":"Call Notice","text":"The amount of notice required to be given by Recipient to the Issuer in order to require all principal and accrued charges due and payable. If not present, the Issuer has no obligation to reduce principal any faster than is indicated by the Minimum Payment. The Call Notice is triggered by affixing a signed Call to the tally. The debt must be satisfied within the specified number of days after the date of the Call. For a fully amortizing debt, a Recipient would register an immediate call, with the number of notice days set to the term of the amortization."},{"title":"Minimum Payment","text":"An amount, or a formula for the smallest amount that may be paid at each Compound Interval."}]'
    )
,(
      'mychips.org',
      'Defaults',
      1,
      'eng',
      '2020-04-01',
      E'\\x371c2072735827601af425e87a04146ab92b75c9dfefd348ece4535363c1879e',
      'Contract Breaches and Conditions of Default',
      'Any of the following actions by either Party constitute a breach of the Agreement and therefore, the Party is deemed to be in Default:',
      '[{"title":"Failure of Duty","text":"Failure to honor any obligation outlined in the Tally, including all its referenced Contract components."},{"title":"False Representation","text":"Determination that any representation given in connection with the Tally is factually untrue."},{"title":"Failure to Commit","text":"Failure to complete a Credit Lift transactions previously committed to as a result of intentional manipulation of software and/or a network."},{"title":"Attempt to Cheat","text":"Failure to complete a Credit Lift honestly and according to the protocol documented and demonstrated by the reference server implementation published by mychips.org."},{"title":"Failure to Honor","text":"Failure to provide sufficient connections to accomplish necessary Credit Lifts, followed by failure to make a Recipient whole by alternative means."}]'
    )
,(
      'mychips.org',
      'Duties_Rights',
      1,
      'eng',
      '2020-04-01',
      E'\\x6d85c4e579a91ecee5449763c972a082ffa337157209a58224be79b8730123cc',
      'Duties of the Parties to Each Other',
      'Each Party has certain duties under this Agreement which duties posit corresponding rights to the other Party as follows:',
      '[{"title":"Cooperation","text":"The Parties enter into this Tally to exchange credit for the purpose of facilitating cooperative commerce and trade with each other as well as others."},{"title":"Good Faith","text":"Each Party shall behave honestly and with integrity in the transactions facilitated by the Tally. Neither Party shall use the Tally to intentionally cheat, defraud, or steal value from the other Party."},{"title":"Competency","text":"Each Party shall take reasonable care to ensure that the other Party is mentally competent to enter into the Contract and its associated transactions. This includes avoiding the receipt of Pledges from those who are too young, too old, or otherwise unable to fully understand the obligations they are entering into."},{"title":"Disclosure","text":"Each Party shall honestly inform the other Party of information relevant to its decision to execute this Tally and/or its associated Pledges. This includes disclosures about any known dangers or deficiences regarding Product purchased by way of the Tally. It also includes known information about one''s ability or past performance in fulfilling Pledges made to other parties."},{"title":"Consent","text":"Each Party shall take reasonable care to ensure that the other Party has entered into this Contract of its own free will and choice."},{"title":"Identity","text":"Each Party shall honestly represent its identity to the other and furnish accurate information adequate for further enforcement of any debt incurred under the Tally."},{"title":"Privacy","text":"Each Party shall take reasonable measures to keep private any information, not already generally available by other means, and which is revealed or discovered in connection with the execution of the Tally."},{"title":"Lift Execution","text":"Each Party shall make reasonable efforts to use software which faithfully executes the MyCHIPs protocol, as published by mychips.org, in good faith. Each Party''s server, having completed the conditional phase of a Lift transaction, shall then make every effort to commit the final phase of that lift in accordance with the agreed upon terms. Use of a current, unmodified, official release of the MyCHIPs software as distributed by mychips.org satisfies the requirements of this section."},{"title":"Resolution by Other Means","text":"Should a Party fail, within 10 days of request, to provide or maintain suitable connections to satisfy an outstanding Pledges by way of Credit Lifts, it shall provide payment upon demand in some other medium satisfactory to the Receiver. This includes payment by a sound government currency in common use by the Receiver such as Dollars or Euros, for example. It could include payment in gold, silver or other precious commodities acceptable to the Receiver. It could also include Product furnished by the Issuer and satisfactory to the Receiver. The Receiver shall not unreasonably refuse a good faith payment offered by such other means."},{"title":"Lift Authority","text":"Each Party authorizes its agent host system to sign Credit Lifts, on behalf of that Party, using the system''s own private/public key. All such lifts executed and signed by the Party''s host system shall be binding upon the Party so long as they conform to the Trading Variables established and signed by the Party in its private counterpart of the Tally. Each Party shall hold its system operator(s) harmless for untinentional errors or losses incurred while using a current, unmodified official release of the MyCHIPs sotware as distributed by mychips.org."},{"title":"Notice of Default","text":"Should one Party find the other Party in Default of this Agreement, it shall give written notice to the Defaulting Party by email, text message or certified mail. Such notice may be as simple as to state the act or circumstance deemed to be a breach, and to request the problem be resolved."},{"title":"Cure of Default","text":"Upon receiving a notice of Default, a Party must make a timely, good faith effort to satisfy the complaint of the noticing Party within 10 days."},{"title":"Publication","text":"If a Default is not cured within 10 days, the non-breaching Party is entitled to publish the identity of the breaching Party and information about the nature of the breach, notwithstanding any obligations regarding privacy. Such publication shall be done solely to inform others who might contemplate entering into a similar transaction with the breaching Party. If a Party has previously published such information and the breaching Party subsequently and satisfactorily cures the breach, the publishing Party shall then also similarly publish information indicating that the breach has been cured."},{"title":"Collateral","text":"If collateral is offered to secure a debt incurred by an Issuer under this Tally, such shall be evidenced by an external agreement such as a deed of trust, a lien or notice of interest. If such agreement is duly executed by the Parties, a Recipient shall enjoy all recourse available by law in using the collateral to fully collect the debt incurred under this Agreement."}]'
    )
,(
      'mychips.org',
      'Ethics',
      1,
      'eng',
      '2020-04-01',
      E'\\x9eacc39eb55712f418fa7798973bb3845d2f4e74ac11d9b1cb2f6c7ba55a5fd3',
      'Ethical Conduct',
      'The credits, or Chits, under a Tally agreement constitute a Pledge of Value, measured in CHIPs, from the Issuer, to the Recipient, which shall be satisfied according to the terms established and cryptographically signed in the Tally. In order for such a Pledge to be a valid, and therefore enforceable, the following conditions must also be met:',
      '[{"title":"Competency","text":"The Issuer is of such age and mental capacity to understand the obligations he/she is entering into."},{"title":"Informed Consent","text":"Both parties are reasonably informed by the other as to all material terms of the transaction. This includes the nature and quality of the Product, as well as the nature and quality of the credit being offered as consideration."},{"title":"Dispute Resolution","text":"In case of a dispute between the Parties over any associated transaction being resolved by legal remedy, the prevailing Party shall be entitled to collect from the losing Party actual incurred damages, plus all collection costs, including attorneys fees."},{"title":"Frivolous Claims","text":"Should any cause of action brought by one Party against the other be shown to be frivolous, or without basis, the penalty shall be increased to two times the actual incurred damages, plus all collection costs, including attorneys fees."},{"title":"Fraud","text":"When intentional fraud can be proven in such a dispute, the penalty shall be increased to three times the actual incurred damages, plus all collection costs, including attorneys fees."},{"title":"Severability","text":"If any portion of this agreement is deemed to be unenforceable by any means, the remaining portions shall remain in full effect."},{"title":"Honor","text":"The debtor agrees to not excuse itself from honoring the agreement by reason of bankruptcy or similar recourse, even though the prevailing law may allow it."},{"title":"Indemnity","text":"The Parties shall hold harmless MyCHIPs.org and all owners and author(s) of the MyCHIPs software for any loss related to the use of the software."},{"title":"Chain of Honor","text":"The obligations related to good faith and honesty made by the Parties also extend to other parties they may be indirectly connected to. For example, it is a breach of this covenant to use your trading relationship under this Tally to defraud another party somewhere else on the network. Each Party agrees to cooperate with the other in the rectification of any fraud or loss which may occur in the course of trading on this Tally. This implies the assignment of contract rights, as applicable such that any unduly harmed party may invoke the rights of each party along a chain of transactions in order to remedy a fraud or undue loss."}]'
    )
,(
      'mychips.org',
      'Free',
      1,
      'eng',
      '2020-04-01',
      E'\\x2d4e1471aa3a772dabbd43159e1c74f27c2e4fdaa1aad16bccc6117ccac07c23',
      'How to Use MyCHIPs at No Cost',
      'End users may use MyCHIPs royalty free on the condition that, in all contracts and transactions, the following contract sections are included in their full force and intent, and abided by:',
      '[{"title":"Recitals","source":"mychips.org/Recitals-1-eng?digest=cb4855eba4518a1af6390f629e738fc0fd0c99b4d44a7208fee2d36c24211f6a"},{"title":"Tally Definition","source":"mychips.org/Tally_Definition-1-eng?digest=18de3cbaa87968bcb043461f8dbe86bb9e954c34270d9c01b641355a8913fc3d"},{"title":"CHIP Definition","source":"mychips.org/CHIP_Definition-1-eng?digest=152fe12217db6307bee73c248b5ee4efc7a4f12ac29aea6add9845e7a4b9afcc"},{"title":"Ethics","source":"mychips.org/Ethics-1-eng?digest=4d7a2c44887ac2fcb70e818795829f46c020740f571a0a5e9133059bbc75f417"}]'
    )
,(
      'mychips.org',
      'Recitals',
      1,
      'eng',
      '2020-04-01',
      E'\\x723cff668a20b4ec730e86d45ec7990d0ce85b2e4991a012c8cf217a6f41718a',
      'Purpose of The Contract',
      'Whereas:',
      '[{"text":"As part of the ordinary course of business, the Parties wish to engage in the exchange of goods and services, hereinafter referred to as Product; and"},{"text":"It is unlikely in any specific transacton that a two-way exchange of Product can be found that is exactly balanced in both time and value and/or is desired by the Parties; and"},{"text":"The Parties desire an efficient way to conduct a single transfer of Product with consideration being given in the form of a Pledge of Value, or a debt, to be honored at some future time and in a form acceptable to the Parties; and"},{"text":"The Parties wanting to issue, receive, and formalize such Pledges of Value, or Credit, in a system of open-account indebtedness and in a digital format for the sake of convenience and accuracy; and"},{"text":"The Parties desire to use the MyCHIPs Protocol as published and explained by mychips.org and demonstrated by its Reference Implementation, to accomplish this;"},{"text":"It is hereby agreed as follows:"}]'
    )
,(
      'mychips.org',
      'Representations',
      1,
      'eng',
      '2020-04-01',
      E'\\x6f5a48ffc58334d6bfc4f3a74e45fa2c58dbfcbed3c581e0f3177db5550d4a47',
      'General Representations of the Parties',
      'The Parties represent as follows about themselves:',
      '[{"title":"Competency","text":"Each Party is of such age and mental capacity to understand the obligations it is entering into by executing this Tally."},{"title":"Financial Capacity","text":"Each Party has the means to satisfy the debts it incurs under the Tally."},{"title":"Network Connections","text":"Each Party will maintain sufficient Client relationships to reasonably facilitate Credit Lifts."},{"title":"Identity","text":"Each Party''s identity as expressed in the Tally is true and accurate."},{"title":"Authority","text":"If a Party is a corporation or other organization, that individual executing the Tally represents that he/she is duly authorized to enter into the Tally on behalf of the organization."},{"title":"Nature of Credit Obligations","text":"This Tally will not be used to document an equity or financial interest where a future return is promised which is a function of the financial success of a venture. Rather, the Tally will be used to record and track debt obligations such as the following:","sections":[{"text":"A note delivered in consumer financing"},{"text":"A note secured by a lien on real property such as a home"},{"text":"A note secured by a lien on a small business or some of its assets"},{"text":"A note relating to a character loan"},{"text":"A note which formalizes an open-account indebtedness incurred in the ordinary course of business"},{"text":"Short-term notes secured by an assignment of accounts receivable"},{"text":"Notes given in connection with loans to a business for current operations"}]}]'
    )
,(
      'mychips.org',
      'Sending_Value',
      1,
      'eng',
      '2020-04-01',
      E'\\xdf3c4a3378b251531ebee3ded36e8a9d4e08f4e03f8e58ff1db9463ea44e2c0b',
      'How Value is Transmitted in a MyCHIPs Network',
      'A Tally contains individual Pledges or Chits, each of which constitutes a promise by the Issuer to deliver value, quantified in CHIPs, to the Recipient at some future time. Since this promise can be offered in exchange for Product, CHIPs can be thought of as money, or a substitute for money. However MyCHIPs resolves these promises in a very different way than credit transactions quantified in traditional money:',
      E'[{"title":"CHIPs Not Transferrable","text":"While most traditional money is transferrable from one party to another, the CHIPs subject to this Contract are not. Rather, Pledges are given by the Issuer to the Recipient, for the sole benefit of the Recipient and no other party. The Recipient does not have the right to reassign an indebtedness to any third party."},{"title":"Credit Lifts","text":"As with traditional money, a Recipient of credit is entitled to be \\"paid\\" within the specified terms. However in the context of MyCHIPs, getting paid means exchanging CHIPs which are held by the Recipient but not wanted, for other CHIPs, issued by other parties which are wanted by the Recipient. This exchange occurs as part of a transaction called a Credit Lift which typically involves multiple parties in a MyCHIPs network and can be accomplished without the need for transferability."},{"title":"Neutral Transaction","text":"As a participant in a Credit Lift, a party might agree to receive back CHIPs it has previously Issued to a Vendor, in return for giving up an equal number of CHIPS back to one of its own Clients. Furthermore, a party can agree to receive CHIPs from a Vendor it plans to obtain Product from in the future, in exchange for issuing CHIPs back to a Client who might want to pay for the party''s own Product in the future. In other words, the Lift transaction creates neither a loss nor a gain for cooperating entities who merely pass value along."},{"title":"Lifts Mutually Beneficial","text":"However, a Credit Lift does produce a substantial benefit for each participant because it has the effect of moving credit in the opposite direction of normal flow. In other words, it relieves pent-up pressure in the network so that regular trading can continue."},{"title":"Lifts Explained","text":"If a party has an accumlation of Stock credits, or assets, and an accumulation of Foil credits, or liabilities, this can be thought of in the context of traditional money as follows: The party has money, or assets, and it has bills to pay, or liabilities. The Credit Lift has the effect of using one''s assets to pay relieve one''s liabilities. In simpler terms: using your money to pay your bills."},{"title":"Trading Fitness","text":"Since the resolution of debt is accomplished by Credit Lifts, Parties to the Tally will need tally relationships with additional parties so Lifts can be accomplished. At a minimum, each MyCHIPs user must have at least one Client and one Vendor relationship. For example, if you are a Client in a tally with a given party, you will also need to be a Vendor in at least one other suitable tally so your Vendor has a viable pathway available for accomplishing the needed Lifts. In terms more applicable to traditional money: If you expect to purchase something on credit, you must have suitable means of income in order to resolve the ensuing debt. In simpler terms: to buy things, you need a job."}]'
    )
,(
      'mychips.org',
      'Tally_Contract',
      1,
      'eng',
      '2020-04-01',
      E'\\xf78db2fd8fe99f4f6bd2a61dc9cade7c2874038bf8756f0f43f895a805ae6013',
      'Tally Contract',
      'This Contract has been incorporated into a MyCHIPs Tally by reference, which includes a digital hash of the contents of the document. This Contract also incorporates further documents by reference, including their digital hashes. All such terms and conditions, including those contained in the Tally itself, this document, and the ones it references, together form the complete Tally Agreement between the Parties.',
      '[{"title":"Recitals","source":"mychips.org/Recitals-1-eng?digest=cb4855eba4518a1af6390f629e738fc0fd0c99b4d44a7208fee2d36c24211f6a"},{"title":"Tally Definition","source":"mychips.org/Tally_Definition-1-eng?digest=18de3cbaa87968bcb043461f8dbe86bb9e954c34270d9c01b641355a8913fc3d"},{"title":"CHIP Definition","source":"mychips.org/CHIP_Definition-1-eng?digest=152fe12217db6307bee73c248b5ee4efc7a4f12ac29aea6add9845e7a4b9afcc"},{"title":"Ethics","source":"mychips.org/Ethics-1-eng?digest=4d7a2c44887ac2fcb70e818795829f46c020740f571a0a5e9133059bbc75f417"},{"title":"Duties and Rights","source":"mychips.org/Duties_Rights-1-eng?digest=050279d41890af77f1d9717a12924b71ead73e7b1365af9e2048bc49a8c477fb"},{"title":"Representations","source":"mychips.org/Representations-1-eng?digest=f0a866200d5c4b211afdc1b18d877f9ceacd1a8d2114605de16ca1fb37417970"},{"title":"Defaults","source":"mychips.org/Defaults-1-eng?digest=f6503a7ddd454daf725d27a3ff2c9ae242efd5521f2883cad528eadab223aff8"},{"title":"Credit Terms","source":"mychips.org/Credit_Terms-1-eng?digest=d81fa07ef9de7326c520b072a9f0322941c0dfafd489d0730a432ae95cc18112"}]'
    )
,(
      'mychips.org',
      'Tally_Definition',
      1,
      'eng',
      '2020-04-01',
      E'\\xc5cccb77998e3bb0c3af1b8b7c60e7ddc680be8662c0d7226161c35df3a712b2',
      'What a Tally is and How it Works',
      'Pledges of Value are tracked by means of a Tally. A Tally is an agreement between two willing Parties, normally stored as a digital electronic record, and by which the Parties document and enforce a series of Pledges of Value, or Chits, made between them.',
      E'[{"title":"Signing Keys","text":"Each Party is in possession of a digital key consisting of a private part and a public part. Each Party is responsible to maintain knowledge and possession of its key and to keep the private portion absolutely confidential. The public part of the key will be used to validate one''s digital signature and so must be shared with the other Party."},{"title":"Signing the Tally","text":"The Parties agree to the terms and conditions incorporated in the Tally by computing a standardized hash from the normalized contents of the Tally, and encrypting that hash using their private key. This act of signing is normally conducted by a user interacting with an application running on a computer or mobile device. By producing a digital signature of the hash of the Tally, the Party is agreeing to all the terms and conditions contained in that Tally, including those that are incorporated by reference. If one Party is in possession of a valid signature of the Tally, which can be verified by the other Party''s public key, this is sufficient proof of the consent of the other Party to the Agreement in its entirety."},{"title":"Stock and Foil","text":"The two Parties to a Tally are distinct with respect to their expected roles. Specifically, the Tally is stored as two complementary counterparts: a Stock, and a Foil, each held or stored by one of the Parties or its agent service provider."},{"title":"Vendor Role","text":"The Party holding the Stock is expected to be the provider of Product most often in the normal course of transactions. This role is referred to as the \\"Vendor.\\""},{"title":"Client Role","text":"The Party holding the Foil is expected to most often be the recipient of Product. This role is referred to as the \\"Client.\\""},{"title":"Typical Examples","text":"For example, if a regular customer establishes a Tally with a merchant to buy Product from that merchant, the customer would hold the Foil and the merchant would hold the Stock. In an employment scenario, the employer will hold the Foil and the Employee will hold the Stock. In less formal trading relationships, the Parties can select their roles of Vendor and Client as seems best to fit the trading relationship."},{"title":"Chits","text":"Each Pledge of Credit contained in a Tally is referred to as a Chit. The Party who is pledging value by the Chit is referred to as the Issuer of credit for that Chit. The Party the pledge is made to is the Receiver of credit. Either Party may unilaterally add valid, digitally signed Chits to the Tally as long as it does so as an Issuer."},{"title":"Authority to Pledge","text":"Neither Party may unilaterally add a Chit as Receiver, or a Chit which would grant value from the other Party to itself. However, either Party may request such a Pledge from the other Party."},{"title":"Net Credit","text":"In spite of the distinct definition of the Vendor and Client, individual Pledges may be made by either Party, to the other Party. For example, a Vendor may also make Pledges to a Client. When added together, the net value of all Pledges contained in the Tally, form a total value for the Tally. Unless that value is zero, it will result in a net indebtedness of one Party to the other."},{"title":"Net Issuer and Recipient","text":"This indebtedness is credit, which can be thought of as a loan, a debt, or and IOU. At any given time, the indebted Party is referred to as the Net Issuer of credit. The other Party is referred to as the Net Recipient of credit."},{"title":"Variable Roles","text":"The roles of Vendor and Client remain constant in the context of the Tally with its two counterparts, Stock and Foil. As the Tally Stock accumulates a positive value, the Client would be the Net Issuer and the Vendor would be the Net Recipient. But the roles of Net Issuer and Net Recipient of credit can become reversed if the balance of the Tally moves from positive to negative."}]'
    )

    on conflict on constraint contracts_pkey do update set 
          published	= EXCLUDED.published,
          digest	= EXCLUDED.digest,
          title		= EXCLUDED.title,
          text		= EXCLUDED.text,
          sections	= EXCLUDED.sections
  ;
insert into base.parm (module, parm, type, v_int, v_text, v_boolean, cmt) values 
  ('mychips', 'site_ent', 'text', null, 'r1', null, 'The ID number of the entity on this site that is the primary administrator.  Internal lifts will be signed by this entity.')

-- Deprecated:
-- ,('mychips', 'user_host', 'text', null, '', null, 'Default IP where mobile application connects.')
-- ,('mychips', 'user_port', 'int', , null, null, 'Default port where mobile user application connects.')
-- ,('mychips', 'peer_agent', 'text', null, '', null, 'Default agent key where peer servers connect.')
-- ,('mychips', 'peer_host', 'text', null, '', null, 'Default network address where peer servers connect.')
-- ,('mychips', 'peer_port', 'int', , null, null, 'Default port where peer servers connect.')

 ,('agents', 'min_time', 'int', 5, null, null, 'Minimum number of minutes between retrying a message to an agent server.')
 ,('agents', 'max_tries', 'int', 100, null, null, 'How many times to retry sending messages to an agent server before giving up.')

 ,('routes', 'life', 'text', null, '60 min', null, 'A valid SQL interval describing how long a route should last before being considered stale')
 ,('routes', 'tries', 'int', 4, null, null, 'The number of times to retry discovering a pathway before giving up')
 ,('routes', 'maxstep', 'int', 10, null, null, 'Do not propagate route queries that have already hopped this many nodes to get to us')
 ,('routes', 'maxquery', 'int', 10, null, null, 'The greatest number of new upstream routes to generate/maintain for each received query')
 ,('routes', 'autoquery', 'boolean', null, null, true, 'The number of times to retry discovering a pathway before giving up')
 
 ,('lifts', 'order', 'text', null, 'bang desc', null, 'An order-by clause to describe how to prioritize lifts when selecting them from the pathways view.  The first result of the query will be the first lift performed.')
 ,('lifts', 'interval', 'int', 10000, null,null, 'The number of milliseconds between sending requests to the database to choose and conduct a lift')
 ,('lifts', 'limit', 'int', 1, null, null, 'The maximum number of lifts the database may perform per request cycle')
 ,('lifts', 'minimum', 'int', 10000, null, null, 'The smallest number of units to consider lifting, absent other guidance from the user or his tallies')

  on conflict on constraint parm_pkey do update
    set type = EXCLUDED.type, v_int = EXCLUDED.v_int, v_text = EXCLUDED.v_text, v_boolean = EXCLUDED.v_boolean, cmt = EXCLUDED.cmt
;
