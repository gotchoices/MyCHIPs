--Schema Creation SQL:
create schema if not exists wm;
create or replace function wm.create_group(grp varchar) returns boolean language plpgsql as $$
  begin
    if not exists (select rolname from pg_roles where rolname = grp) then
      execute 'create role ' || grp || ';'; return true;
    end if;
    return false;
  end;
$$;
create or replace function wm.release() returns int stable language plpgsql as $$
  begin return 1; end;
$$;
create type audit_type as enum ('update','delete');
create schema base;
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
create table wm.message_text (
mt_sch		name
  , mt_tab		name
  , code		varchar
  , language		varchar not null
  , title		varchar		-- brief title for error message
  , help		varchar		-- longer help description
  , primary key (mt_sch, mt_tab, code, language)
);
create view wm.role_members as select ro.rolname as role, me.rolname  as member
    from        	pg_auth_members am
    join        	pg_authid       ro on ro.oid = am.roleid
    join        	pg_authid       me on me.oid = am.member;
create table wm.table_style (
ts_sch		name
  , ts_tab		name
  , sw_name		varchar not null
  , sw_value		varchar not null
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
create schema wylib;
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
create function base.priv_role(name,varchar,int) returns boolean security definer language plpgsql stable as $$
    declare
      trec	record;
    begin
      if $1 = current_database() then		-- Always true for DBA
        return true;
      end if;
      for trec in 
        select * from (select role, member, (regexp_split_to_array(role,'_'))[1] as rpriv,
                                            (regexp_split_to_array(role,'_'))[2] as rlevel
            from wm.role_members where member = $1) sq where sq.rpriv = $2 or sq.rlevel = '0' order by sq.rlevel desc loop

          if trec.rpriv = $2 and trec.rlevel >= $3 then
              return true;
          elsif trec.rlevel = 0 then
              if base.priv_role(trec.role,$2,$3) then return true; end if;
          end if;
        end loop;
        return false;
    end;
$$;
create operator =* (leftarg = text,rightarg = text,procedure = eqnocase, negator = !=*);
create function mychips.agent_tf_change() returns trigger language plpgsql security definer as $$
    begin
      if (new.module = 'agent') then
        perform pg_notify('mychips_agent', format('{"target":"%s", "oper":"%s", "time":"%s"}', coalesce(TG_ARGV[0],'Unknown'), TG_OP, transaction_timestamp()::text));
      end if;
      return null;
    end;
$$;
create function mychips.change_tf_notify() returns trigger language plpgsql security definer as $$
    begin
      perform pg_notify('mychips_admin', format('{"target":"%s", "oper":"%s", "time":"%s"}', coalesce(TG_ARGV[0],'Unknown'), TG_OP, transaction_timestamp()::text));
      return null;
    end;
$$;
create function mychips.chit_state(isdebit boolean, request text, signature text) returns text immutable language plpgsql as $$
    begin return
      case when isdebit then
        case when signature = 'void'		then 'peerDecline'
           when signature is not null		then 'peerValid'
           when request = 'userRequest'		then 'userRequest'
           when request is null			then 'userInvoice'
           else					     'undefined'	end
      else	--is a credit
        case when signature = 'void' then
        case when request = 'userDecline'	then 'userDecline'
             when request is null		then 'userVoid'
             else				     'undefined'    end
           when signature is null then
        case when request is null		then 'peerInvoice'
             else				     'undefined'    end
           when request = 'userAgree'		then 'userAgree'
           when request = 'userDraft'		then 'userDraft'
           when request is null			then 'userValid'
      else     					     'undefined'	end
      end;
    end;
$$;
create function mychips.chits_tf_cache() returns trigger language plpgsql security definer as $$
    declare
      trec	record;
    begin
      if TG_OP = 'DELETE' then trec = old; else trec = new; end if;
      update mychips.tallies set units_c = (select coalesce(sum(units),0) from mychips.chits where chit_ent = trec.chit_ent and chit_seq = trec.chit_seq) where tally_ent = trec.chit_ent and tally_seq = trec.chit_seq;
      return null;
    end;
$$;
create function mychips.contract_url(dom text, nam text, ver int, lan text, dig text) returns text immutable language sql as $$
    select dom || '/' || nam || '-' || ver::text || '-' || lan || case when dig is null then '' else '?' || dig end;
$$;
create function mychips.lifts_tf_change() returns trigger language plpgsql security definer as $$
    begin
      if (new.module = 'lifts') then
        perform pg_notify('mychips_lifts', format('{"target":"%s", "oper":"%s", "time":"%s"}', coalesce(TG_ARGV[0],'Unknown'), TG_OP, transaction_timestamp()::text));
      end if;
      return null;
    end;
$$;
create function mychips.tally_state(status text, request text, user_sig text, part_sig text, total bigint) returns text immutable language plpgsql as $$
    begin
      return case when status = 'void' and request is null	then 'void'
         when status = 'void' and request = 'draft'		then 'userDraft'
         when status = 'draft' and request is null then
           case when user_sig is not null and part_sig is null	then 'userProffer'
                when part_sig is not null and user_sig is null	then 'peerProffer'
           else 'undefined' end
         when status = 'draft' and request = 'void'		then 'userVoid'
         when status = 'draft' and request = 'open'		then 'accepted'
         when status = 'open' and request is null		then 'open'
         when status = 'open' and request = 'close'		then 'userClose'
         when status = 'close' and request is null then
             case when total = 0 then 'closed' else 'closing' end
         else 'undefined' end;
    end;
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
  , nd.adsrc		as def
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
  , conn_pub	text
  , ent_inact	boolean		not null default false
  , country	varchar(3)	not null default 'US' references base.country on update cascade
  , tax_id	text          , unique(country, tax_id)
  , bank	text
  , proxy	text		constraint "!ent.ent.OPR" check (proxy != id)


    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.priv_has(varchar,int) returns boolean language sql stable as $$
      select base.priv_role(session_user,$1,$2);
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
  , coalesce(ct.language, nt.language, 'en')	as language
  , coalesce(ct.title, nt.title, cd.cdt_col)	as title
  , coalesce(ct.help, nt.help)			as help
  , cd.cdt_sch in ('pg_catalog','information_schema') as system
  from		wm.column_data cd
    left join	wm.column_text nt	on nt.ct_sch = cd.nat_sch and nt.ct_tab = cd.nat_tab and nt.ct_col = cd.nat_col
    left join	wm.column_text ct	on ct.ct_sch = cd.cdt_sch and ct.ct_tab = cd.cdt_tab and ct.ct_col = cd.cdt_col 	--(No!) and ct.language = nt.language

    where	cd.cdt_col != '_oid'
    and		cd.field >= 0;
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
  , coalesce(vt.language, nt.language, 'en')	as language
  , coalesce(vt.title, nt.title, cd.cdt_col)	as title
  , coalesce(vt.help, nt.help)			as help
  from		wm.column_data cd
    left join	wm.column_text vt	on vt.ct_sch = cd.cdt_sch and vt.ct_tab = cd.cdt_tab and vt.ct_col = cd.cdt_col
    left join	wm.column_text nt	on nt.ct_sch = cd.nat_sch and nt.ct_tab = cd.nat_tab and nt.ct_col = cd.nat_col

    where	cd.cdt_col != '_oid'
    and		cd.field >= 0;
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
create view wm.table_data as select
    ns.nspname				as td_sch
  , cl.relname				as td_tab
  , ns.nspname || '.' || cl.relname	as obj
  , cl.relkind				as tab_kind
  , cl.relhaspkey			as has_pkey
  , cl.relnatts				as cols
  , ns.nspname in ('pg_catalog','information_schema') as system
  , kd.pkey
  from		pg_class	cl
  join		pg_namespace	ns	on cl.relnamespace = ns.oid
  left join	(select cdt_sch,cdt_tab,array_agg(cdt_col) as pkey from (select cdt_sch,cdt_tab,cdt_col,field from wm.column_data where pkey order by 1,2,4) sq group by 1,2) kd on kd.cdt_sch = ns.nspname and kd.cdt_tab = cl.relname
  where		cl.relkind in ('r','v');
create table base.addr (
addr_ent	text		references base.ent on update cascade on delete cascade
  , addr_seq	int	      , primary key (addr_ent, addr_seq)
  , addr_spec	text		not null
  , addr_type	text		not null check(addr_type in ('phys','mail','bill','ship'))
  , addr_prim	boolean		not null default false constraint "!base.addr.CPA" check(case when addr_inact is true then addr_prim is false end)
  , addr_cmt	text
  , addr_inact	boolean		not null default false
  , city	text
  , state	text
  , pcode	text
  , country	varchar(3)	constraint "!base.addr.CCO" not null default 'US' references base.country on update cascade
  , unique (addr_ent, addr_seq, addr_type)		-- Needed for addr_prim FK to work

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table base.comm (
comm_ent	text		references base.ent on update cascade on delete cascade
  , comm_seq	int	      , primary key (comm_ent, comm_seq)
  , comm_spec	text
  , comm_type	text		not null check(comm_type in ('phone','email','cell','fax','text','web','pager','other'))
  , comm_prim	boolean		not null default false constraint "!base.comm.CPC" check(case when comm_inact is true then comm_prim is false end)
  , comm_cmt	text
  , comm_inact	boolean		not null default false
  , unique (comm_ent, comm_seq, comm_type)		-- Needed for comm_prim FK to work

    
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
          , a_column	varchar		not null
          , a_value	varchar
     	  , a_reason	text
          , primary key (id,a_seq)
);
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
            execute 'drop user ' || old.username;
        end if;
        return old;
    end;
$$;
create function base.ent_tf_id() returns trigger language plpgsql as $$
    declare
      min_num	int;
    begin
      if new.ent_num is null then
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
        new.conn_pub = false;
      end if;
      if TG_OP = 'UPDATE' then
        if new.username != old.username then	-- if trying to change an existing username

          execute 'drop user ' || '"' || old.username || '"';
        end if;
      end if;

      if new.username is not null and not exists (select usename from pg_shadow where usename = new.username) then

        execute 'create user ' || '"' || new.username || '"';
        for trec in select * from base.priv where grantee = new.username loop
          execute 'grant "' || trec.priv_level || '" to ' || trec.grantee;
        end loop;
      elseif new.username is null and exists (select usename from pg_shadow where usename = new.username) then

        execute 'drop user ' || '"' || new.username || '"';
      end if;
      return new;
    end;
$$;
create view base.ent_v as select e.id, e.ent_num, e.conn_pub, e.ent_name, e.ent_type, e.ent_cmt, e.fir_name, e.mid_name, e.pref_name, e.title, e.gender, e.marital, e.born_date, e.username, e.ent_inact, e.country, e.tax_id, e.bank, e.proxy, e.crt_by, e.mod_by, e.crt_date, e.mod_date
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

    create rule base_ent_v_insert as on insert to base.ent_v
        do instead insert into base.ent (ent_name, ent_type, ent_cmt, fir_name, mid_name, pref_name, title, gender, marital, born_date, username, ent_inact, country, tax_id, bank, proxy, crt_by, mod_by, crt_date, mod_date) values (new.ent_name, new.ent_type, new.ent_cmt, new.fir_name, new.mid_name, new.pref_name, new.title, new.gender, new.marital, new.born_date, new.username, new.ent_inact, new.country, new.tax_id, new.bank, new.proxy, session_user, session_user, current_timestamp, current_timestamp);
    create rule base_ent_v_update as on update to base.ent_v
        do instead update base.ent set ent_name = new.ent_name, ent_cmt = new.ent_cmt, fir_name = new.fir_name, mid_name = new.mid_name, pref_name = new.pref_name, title = new.title, gender = new.gender, marital = new.marital, born_date = new.born_date, username = new.username, ent_inact = new.ent_inact, country = new.country, tax_id = new.tax_id, bank = new.bank, proxy = new.proxy, mod_by = session_user, mod_date = current_timestamp where id = old.id;
    create rule base_ent_v_delete as on delete to base.ent_v
        do instead delete from base.ent where id = old.id;
create index base_ent_x_ent_type_ent_num on base.ent (ent_type,ent_num);
create index base_ent_x_proxy on base.ent (proxy);
create index base_ent_x_username on base.ent (username);
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
grantee	varchar		references base.ent (username) on update cascade on delete cascade
  , priv	varchar		
  , level	int		not null
  , priv_level	varchar		not null
  , cmt		varchar
  , primary key (grantee, priv)
);
create table base.token (
token_ent	text		references base.ent on update cascade on delete cascade
  , token_seq	int	      , primary key (token_ent, token_seq)
  , token	text		not null unique
  , allows	varchar(8)	not null
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
create table mychips.contracts (
domain	varchar		not null
  , name	varchar		not null
  , version	int		not null default 1 constraint "!mychips.contracts.BVN" check (version >= 1)
  , language	varchar		not null references base.language on update cascade on delete restrict
  , published	date	      , constraint "!mychips.contracts.PBC" check (published is null or (sections is not null and digest is not null))
  , title	varchar		not null
  , tag		varchar
  , text	varchar
  , digest	varchar	      , unique (digest)
  , sections	jsonb
  , primary key(domain, name, version, language)
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.peers (
peer_ent	text		primary key references base.ent on update cascade on delete cascade
  , peer_cdi	text		
  , peer_hid	text		
  , peer_pub	text		
  , peer_inet	inet
  , peer_port	int
  , peer_cmt	text
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.tallies (
tally_ent	text		references base.ent on update cascade on delete cascade
  , tally_seq	int	      , primary key (tally_ent, tally_seq)
  , tally_guid	uuid		not null
  , tally_type	text		not null default 'stock' check(tally_type in ('stock','foil'))
  , tally_date	timestamptz	not null default current_timestamp
  , version	int		not null default 1 constraint "!mychips.tallies.VER" check (version > 0)
  , partner	text		references base.ent on update cascade on delete restrict
  , status	text		not null default 'void' check(status in ('void','draft','open','close'))
  , request	text		check(request is null or request in ('void','draft','open','close'))
  , comment	text
  , user_sig	text
  , part_sig	text
  , contract	jsonb		-- not null
  , stock_terms	jsonb
  , foil_terms	jsonb
  , bal_target	bigint		not null default 0
  , lift_marg	float		not null default 0 constraint "!mychips.tallies.LMG" check (lift_marg > -1 and lift_marg < 1)
  , drop_marg	float		not null default 1 constraint "!mychips.tallies.DMG" check (drop_marg >= 0 and drop_marg <= 1)
  , dr_limit	bigint		not null default 0
  , cr_limit	bigint		not null default 0
  , units_c	bigint		default 0 not null
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.tokens (
token_ent	text		references base.ent on update cascade on delete cascade
  , token_seq	int	      , primary key (token_ent, token_seq)
  , token	text		not null unique
  , allows	text		not null default 'stock' constraint "!mychips.tokens.ITA" check (allows in ('stock','foil','query','user'))
  , token_cmt	text		
  , used	boolean		not null default false
  , exp_date	timestamp(0)	default current_timestamp + '45 minutes'
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.users (
user_ent	text		primary key references base.ent on update cascade on delete cascade
  , user_inet	inet
  , user_port	int		
  , user_stat	varchar		not null default 'lck' constraint "!mychips.users.UST" check (user_stat in ('act','lck','off'))
  , user_cmt	varchar
  , host_id	varchar
    
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
create table base.addr_prim (
prim_ent	text
  , prim_seq	int
  , prim_type	text
  , primary key (prim_ent, prim_seq, prim_type)
  , foreign key (prim_ent, prim_seq, prim_type) references base.addr (addr_ent, addr_seq, addr_type)
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
        if new.addr_seq is null then			-- Generate unique sequence for new addrunication entry
            select into new.addr_seq coalesce(max(addr_seq),0)+1 from base.addr where addr_ent = new.addr_ent;
        end if;
        if new.addr_inact then				-- Can't be primary if inactive
            new.addr_prim = false;
        elsif not exists (select addr_seq from base.addr where addr_ent = new.addr_ent and addr_type = new.addr_type) then
            new.addr_prim = true;
        end if;
        if new.addr_prim then				-- If this is primary, all others are now not
            set constraints base.addr_prim_prim_ent_fkey deferred;
            perform base.addr_make_prim(new.addr_ent, new.addr_seq, new.addr_type);
        end if;
        new.addr_prim = false;
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
create view base.addr_v_flat as select e.id, a0.addr_spec as "phys_addr", a0.city as "phys_city", a0.state as "phys_state", a0.pcode as "phys_pcode", a0.country as "phys_country", a1.addr_spec as "mail_addr", a1.city as "mail_city", a1.state as "mail_state", a1.pcode as "mail_pcode", a1.country as "mail_country", a2.addr_spec as "bill_addr", a2.city as "bill_city", a2.state as "bill_state", a2.pcode as "bill_pcode", a2.country as "bill_country", a3.addr_spec as "ship_addr", a3.city as "ship_city", a3.state as "ship_state", a3.pcode as "ship_pcode", a3.country as "ship_country" from base.ent e left join base.addr a0 on a0.addr_ent = e.id and a0.addr_type = 'phys' and a0.addr_prim left join base.addr a1 on a1.addr_ent = e.id and a1.addr_type = 'mail' and a1.addr_prim left join base.addr a2 on a2.addr_ent = e.id and a2.addr_type = 'bill' and a2.addr_prim left join base.addr a3 on a3.addr_ent = e.id and a3.addr_type = 'ship' and a3.addr_prim;
create index base_addr_x_addr_type on base.addr (addr_type);
create table base.comm_prim (
prim_ent	text
  , prim_seq	int
  , prim_type	text
  , primary key (prim_ent, prim_seq, prim_type)
  , foreign key (prim_ent, prim_seq, prim_type) references base.comm (comm_ent, comm_seq, comm_type)
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
            select into new.comm_seq coalesce(max(comm_seq),0)+1 from base.comm where comm_ent = new.comm_ent;
        end if;
        if new.comm_inact then				-- Can't be primary if inactive
            new.comm_prim = false;
        elsif not exists (select comm_seq from base.comm where comm_ent = new.comm_ent and comm_type = new.comm_type) then
            new.comm_prim = true;
        end if;
        if new.comm_prim then				-- If this is primary, all others are now not
            set constraints base.comm_prim_prim_ent_fkey deferred;
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
create index base_ent_audit_x_a_column on base.ent_audit (a_column);
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
create function base.ent_tf_audit_d() --Call when a record is deleted in the audited table
          returns trigger language plpgsql security definer as $$
            begin
                insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','ent_name',old.ent_name::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','ent_type',old.ent_type::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','ent_cmt',old.ent_cmt::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','fir_name',old.fir_name::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','mid_name',old.mid_name::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','pref_name',old.pref_name::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','title',old.title::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','gender',old.gender::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','marital',old.marital::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','born_date',old.born_date::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','username',old.username::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','ent_inact',old.ent_inact::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','country',old.country::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','tax_id',old.tax_id::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','bank',old.bank::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','proxy',old.proxy::varchar);
                return old;
            end;
        $$;
create function base.ent_tf_audit_u() --Call when a record is updated in the audited table
          returns trigger language plpgsql security definer as $$
            begin
                if new.ent_name is distinct from old.ent_name then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','ent_name',old.ent_name::varchar); end if;
		if new.ent_type is distinct from old.ent_type then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','ent_type',old.ent_type::varchar); end if;
		if new.ent_cmt is distinct from old.ent_cmt then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','ent_cmt',old.ent_cmt::varchar); end if;
		if new.fir_name is distinct from old.fir_name then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','fir_name',old.fir_name::varchar); end if;
		if new.mid_name is distinct from old.mid_name then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','mid_name',old.mid_name::varchar); end if;
		if new.pref_name is distinct from old.pref_name then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','pref_name',old.pref_name::varchar); end if;
		if new.title is distinct from old.title then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','title',old.title::varchar); end if;
		if new.gender is distinct from old.gender then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','gender',old.gender::varchar); end if;
		if new.marital is distinct from old.marital then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','marital',old.marital::varchar); end if;
		if new.born_date is distinct from old.born_date then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','born_date',old.born_date::varchar); end if;
		if new.username is distinct from old.username then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','username',old.username::varchar); end if;
		if new.ent_inact is distinct from old.ent_inact then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','ent_inact',old.ent_inact::varchar); end if;
		if new.country is distinct from old.country then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','country',old.country::varchar); end if;
		if new.tax_id is distinct from old.tax_id then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','tax_id',old.tax_id::varchar); end if;
		if new.bank is distinct from old.bank then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','bank',old.bank::varchar); end if;
		if new.proxy is distinct from old.proxy then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','proxy',old.proxy::varchar); end if;
                return new;
            end;
        $$;
create trigger base_ent_tr_dacc -- do after individual grants are deleted
    after delete on base.ent for each row execute procedure base.ent_tf_dacc();
create trigger base_ent_tr_id before insert or update on base.ent for each row execute procedure base.ent_tf_id();
create trigger base_ent_tr_iuacc before insert or update on base.ent for each row execute procedure base.ent_tf_iuacc();
create view base.ent_v_pub as select id, std_name, ent_type, ent_num, username, ent_inact, crt_by, mod_by, crt_date, mod_date from base.ent_v;
create table base.parm_audit (
module text,parm text
          , a_seq	int		check (a_seq >= 0)
          , a_date	timestamptz	not null default current_timestamp
          , a_by	name		not null default session_user references base.ent (username) on update cascade
          , a_action	audit_type	not null default 'update'
          , a_column	varchar		not null
          , a_value	varchar
     	  , a_reason	text
          , primary key (module,parm,a_seq)
);
create function base.parm_boolean(m text, p text) returns boolean language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'boolean';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_boolean;
    end;
$$;
create function base.parm_date(m text, p text) returns date language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'date';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_date;
    end;
$$;
create function base.parm_float(m text, p text) returns float language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'float';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_float;
    end;
$$;
create function base.parm_int(m text, p text) returns int language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'int';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_int;
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
create function base.parm_text(m text, p text) returns int language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'text';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
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
        new.priv_level := new.priv || '_' || new.level;
        
        if TG_OP = 'UPDATE' then
            if new.grantee != old.grantee or new.priv != old.priv or new.level != old.level then
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
    left join	(select member,array_agg(role) as priv_list from wm.role_members group by 1) g on g.member = p.priv_level;

    create rule base_priv_v_insert as on insert to base.priv_v
        do instead insert into base.priv (grantee, priv, level, cmt) values (new.grantee, new.priv, new.level, new.cmt);
    create rule base_priv_v_update as on update to base.priv_v
        do instead update base.priv set grantee = new.grantee, priv = new.priv, level = new.level, cmt = new.cmt where grantee = old.grantee and priv = old.priv;
    create rule base_priv_v_delete as on delete to base.priv_v
        do instead delete from base.priv where grantee = old.grantee and priv = old.priv;
create function base.std_name(name) returns text language sql security definer stable as $$
    select std_name from base.ent_v where username = $1;
$$;
create function base.std_name(text) returns text language sql security definer stable as $$
    select std_name from base.ent_v where id = $1;
$$;
create function base.token_login(uid text) returns base.token language sql as $$
    insert into base.token (token_ent, allows) values (uid, 'login') returning *;
$$;
create function base.token_tf_seq() returns trigger security definer language plpgsql as $$
    begin
      if new.token_seq is null then
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
create trigger mychips_agent_tr_change after insert or update on base.parm for each row execute procedure mychips.agent_tf_change();
create table mychips.chits (
chit_ent	text
  , chit_seq	int	      , foreign key (chit_ent, chit_seq) references mychips.tallies on update cascade on delete cascade
  , chit_idx	int	      , primary key (chit_ent, chit_seq, chit_idx)
  , chit_guid	uuid		not null
  , chit_type	text		not null default 'tran' check(chit_type in ('gift','lift','loan','tran'))
  , chit_date	timestamptz	not null default current_timestamp
  , request	text		check(request is null or request in ('userDraft','userRequest','userAgree','userDecline'))
  , signature	text
  , units	bigint		not null
  , pro_quo	text
  , memo	text
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.confirms (
conf_ent	text
  , conf_seq	int	      , foreign key (conf_ent, conf_seq) references mychips.tallies on update cascade on delete cascade
  , conf_idx	int	      , primary key (conf_ent, conf_seq, conf_idx)
  , conf_id	uuid
  , conf_date	timestamptz	not null default current_timestamp
  , sum		bigint		not null
  , signature	text
);
create function mychips.contracts_tf_bi() returns trigger language plpgsql security definer as $$
    begin
      if new.version is null then
        select into new.version coalesce(version,0)+1 from mychips.contracts where domain = new.domain and name = new.name and version = new.version and language = new.language;
      end if;
      return new;
    end;
$$;
create function mychips.contracts_tf_bu() returns trigger language plpgsql security definer as $$
    begin
      if old.published is not null then		-- Can't edit published contracts
        return null;
      end if;
      if new.version < new.version then		-- Can't go back on versions
        new.version = old.version;		
      end if;
      return new;
    end;
$$;
create view mychips.contracts_v as select c.domain, c.name, c.version, c.language, c.title, c.text, c.tag, c.digest, c.sections, c.published, c.crt_by, c.mod_by, c.crt_date, c.mod_date
  , mychips.contract_url(c.domain, c.name, c.version, c.language, c.digest) as source
  , jsonb_build_object(
      'domain',		c.domain
    , 'name',		c.name
    , 'version',	c.version
    , 'language',	c.language
    , 'published',	c.published
    , 'title',		c.title
    , 'tag',		c.tag
    , 'text',		c.text
    , 'digest',		c.digest
    , 'sections',	c.sections
    ) as json

    from	mychips.contracts c;

    ;
    ;
    create rule mychips_contracts_v_delete as on delete to mychips.contracts_v
        do instead delete from mychips.contracts where domain = old.domain and name = old.name and version = old.version and language = old.language;
create trigger mychips_lifts_tr_change after insert or update on base.parm for each row execute procedure mychips.lifts_tf_change();
create view mychips.paths_v as with recursive tally_path(id, length, pids, uuids, cycle, circuit, cost, min, max) as (
    select	p.peer_ent, 1, array[p.peer_ent], '{}'::uuid[], false, false, 1.00::float, null::bigint, null::bigint
    from	mychips.peers p 
    where not p.peer_ent isnull
  union all
    select t.tally_ent					as id
      , tp.length + 1					as length
      , tp.pids || t.tally_ent				as pids
      , tp.uuids || t.tally_guid			as uuids
      , t.tally_ent = any(tp.pids)			as cycle
      , tp.pids[1] = t.tally_ent			as circuit
      , tp.cost * (1 + t.lift_marg)			as cost
      , coalesce(least(t.units_c,tp.min), t.units_c)	as min
      , coalesce(greatest(t.units_c,tp.max), t.units_c)	as max
    from	mychips.tallies t
    join	tally_path	tp on tp.id = t.partner and not tp.cycle
    where	t.tally_type = 'stock'
  ) select tpr.id
    , tpr.length
    , tpr.pids[2:array_upper(tpr.pids,1)] as path
    , tpr.uuids
    , tpr.cycle
    , tpr.circuit
    , tpr.cost
    , tpr.min
    , tpr.max
    , tpr.length * tpr.min as bang
  from tally_path tpr;
create trigger mychips_peers_tr_change after insert or update or delete on mychips.peers for each statement execute procedure mychips.change_tf_notify('peers');
create view mychips.peers_v as select 
    ee.id, ee.ent_name, ee.ent_type, ee.ent_cmt, ee.fir_name, ee.mid_name, ee.pref_name, ee.title, ee.gender, ee.marital, ee.born_date, ee.username, ee.ent_inact, ee.country, ee.tax_id, ee.bank, ee.proxy, ee.std_name, ee.frm_name, ee.giv_name, ee.cas_name
  , pe.peer_ent, pe.peer_cdi, pe.peer_hid, pe.peer_pub, pe.peer_inet, pe.peer_port, pe.peer_cmt, pe.crt_by, pe.mod_by, pe.crt_date, pe.mod_date
  , host(peer_inet) || ':' || peer_port	as peer_sock

    from	base.ent_v	ee
    left join	mychips.peers	pe on pe.peer_ent = ee.id;

    
    
    create rule mychips_peers_v_delete_0 as on delete to mychips.peers_v do instead nothing;
    create rule mychips_peers_v_delete_1 as on delete to mychips.peers_v where (old.crt_by = session_user and (current_timestamp - old.crt_date) < '2 hours'::interval) or base.priv_has('userim',3) do instead delete from mychips.peers where peer_ent = old.peer_ent;
create function mychips.tallies_tf_seq() returns trigger language plpgsql security definer as $$
    begin
        if new.tally_seq is null then
            select into new.tally_seq coalesce(max(tally_seq),0)+1 from mychips.tallies where tally_ent = new.tally_ent;
        end if;
        return new;
    end;
$$;
create trigger mychips_tallies_tr_change after insert or update or delete on mychips.tallies for each statement execute procedure mychips.change_tf_notify('tallies');
create index mychips_tallies_x_tally_date on mychips.tallies (tally_date);
create index mychips_tallies_x_tally_guid on mychips.tallies (tally_guid);
create index mychips_tallies_x_tally_type on mychips.tallies (tally_type);
create function mychips.tally_find(ent int, part int, typ text) returns int immutable language plpgsql as $$
    declare
      trec record;
    begin
      select into trec * from mychips.tallies where tally_ent = ent and status = 'open' and tally_type = typ and partner = part order by crt_date desc limit 1;
      return trec.tally_seq;
    end;
$$;
create function mychips.token_tf_seq() returns trigger security definer language plpgsql as $$
    begin
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
      update mychips.tokens set used = 't' where token_ent = new.token_ent and token_seq != new.token_seq and not used;
      return new;
    end;
$$;
create view mychips.users_v as select 
    ee.id, ee.ent_name, ee.ent_type, ee.ent_cmt, ee.fir_name, ee.mid_name, ee.pref_name, ee.title, ee.gender, ee.marital, ee.born_date, ee.username, ee.ent_inact, ee.country, ee.tax_id, ee.bank, ee.proxy, ee.ent_num, ee.std_name, ee.frm_name, ee.giv_name, ee.cas_name, ee.age, ee.conn_pub
  , pe.peer_ent, pe.peer_cdi, pe.peer_hid, pe.peer_pub, pe.peer_inet, pe.peer_port, pe.peer_cmt
  , ue.user_ent, ue.user_inet, ue.user_port, ue.user_stat, ue.user_cmt, ue.host_id, ue.crt_by, ue.mod_by, ue.crt_date, ue.mod_date
  , host(user_inet) || ':' || user_port	as user_sock
  , host(peer_inet) || ':' || peer_port	as peer_sock

    from	base.ent_v	ee
    left join	mychips.peers	pe on pe.peer_ent = ee.id
    left join	mychips.users	ue on ue.user_ent = ee.id;

    
    
    create rule mychips_users_v_delete_0 as on delete to mychips.users_v do instead nothing;
    create rule mychips_users_v_delete_1 as on delete to mychips.users_v where (old.crt_by = session_user and (current_timestamp - old.crt_date) < '2 hours'::interval) or base.priv_has('userim',3) do instead delete from mychips.users where user_ent = old.user_ent;
create table wylib.data (
ruid	serial primary key
  , component	text
  , name	text
  , descr	text
  , access	varchar(5)	not null default 'read' constraint "!wylib.data.IAT" check (access in ('priv', 'read', 'write'))
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
create trigger base_addr_tr_bu before update on base.addr for each row execute procedure base.addr_tf_bu();
create view base.addr_v as select a.addr_ent, a.addr_seq, a.addr_spec, a.city, a.state, a.pcode, a.country, a.addr_cmt, a.addr_type, a.addr_inact, a.crt_by, a.mod_by, a.crt_date, a.mod_date
      , oe.std_name
      , ap.prim_seq is not null and ap.prim_seq = a.addr_seq	as addr_prim

    from	base.addr	a
    join	base.ent_v	oe	on oe.id = a.addr_ent
    left join	base.addr_prim	ap	on ap.prim_ent = a.addr_ent and ap.prim_type = a.addr_type;

    ;
    ;
    create rule base_addr_v_delete as on delete to base.addr_v
        do instead delete from base.addr where addr_ent = old.addr_ent and addr_seq = old.addr_seq;
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
create view base.comm_v as select c.comm_ent, c.comm_seq, c.comm_type, c.comm_spec, c.comm_cmt, c.comm_inact, c.crt_by, c.mod_by, c.crt_date, c.mod_date
      , oe.std_name
      , cp.prim_seq is not null and cp.prim_seq = c.comm_seq	as comm_prim

    from	base.comm	c
    join	base.ent_v	oe	on oe.id = c.comm_ent
    left join	base.comm_prim	cp	on cp.prim_ent = c.comm_ent and cp.prim_type = c.comm_type;

    ;
    ;
    create rule base_comm_v_delete as on delete to base.comm_v
        do instead delete from base.comm where comm_ent = old.comm_ent and comm_seq = old.comm_seq;
create trigger base_ent_audit_tr_bi before insert on base.ent_audit for each row execute procedure base.ent_audit_tf_bi();
create trigger base_ent_link_tf_check before insert or update on base.ent_link for each row execute procedure base.ent_link_tf_check();
create trigger base_ent_tr_audit_d after delete on base.ent for each row execute procedure base.ent_tf_audit_d();
create trigger base_ent_tr_audit_u after update on base.ent for each row execute procedure base.ent_tf_audit_u();
create function base.parm_audit_tf_bi() --Call when a new audit record is generated
          returns trigger language plpgsql security definer as $$
            begin
                if new.a_seq is null then		--Generate unique audit sequence number
                    select into new.a_seq coalesce(max(a_seq)+1,0) from base.parm_audit where module = new.module and parm = new.parm;
                end if;
                return new;
            end;
        $$;
create index base_parm_audit_x_a_column on base.parm_audit (a_column);
create function base.parmsett(m text, p text, v text, t text default null) returns text language plpgsql as $$
    begin
      return base.parmset(m,p,v,t);
    end;
$$;
create function base.parm(m text, p text) returns text language sql stable as $$ select value from base.parm_v where module = m and parm = p; $$;
create function base.parm_tf_audit_d() --Call when a record is deleted in the audited table
          returns trigger language plpgsql security definer as $$
            begin
                insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'delete','cmt',old.cmt::varchar);
		insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'delete','v_int',old.v_int::varchar);
		insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'delete','v_date',old.v_date::varchar);
		insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'delete','v_text',old.v_text::varchar);
		insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'delete','v_float',old.v_float::varchar);
		insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'delete','v_boolean',old.v_boolean::varchar);
                return old;
            end;
        $$;
create function base.parm_tf_audit_u() --Call when a record is updated in the audited table
          returns trigger language plpgsql security definer as $$
            begin
                if new.cmt is distinct from old.cmt then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'update','cmt',old.cmt::varchar); end if;
		if new.v_int is distinct from old.v_int then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'update','v_int',old.v_int::varchar); end if;
		if new.v_date is distinct from old.v_date then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'update','v_date',old.v_date::varchar); end if;
		if new.v_text is distinct from old.v_text then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'update','v_text',old.v_text::varchar); end if;
		if new.v_float is distinct from old.v_float then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'update','v_float',old.v_float::varchar); end if;
		if new.v_boolean is distinct from old.v_boolean then insert into base.parm_audit (module,parm,a_date,a_by,a_action,a_column,a_value) values (old.module, old.parm,transaction_timestamp(),session_user,'update','v_boolean',old.v_boolean::varchar); end if;
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
            update base.parm set cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_int = new.value::int where module = old.module and parm = old.parm;
        when old.type = 'date' then
            update base.parm set cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_date = new.value::date where module = old.module and parm = old.parm;
        when old.type = 'text' then
            update base.parm set cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_text = new.value::text where module = old.module and parm = old.parm;
        when old.type = 'float' then
            update base.parm set cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_float = new.value::float where module = old.module and parm = old.parm;
        when old.type = 'boolean' then
            update base.parm set cmt = new.cmt, mod_by = session_user, mod_date = current_timestamp, v_boolean = new.value::boolean where module = old.module and parm = old.parm;
        end case;
        return new;
    end;
$$;
create function base.pop_role(rname varchar) returns void security definer language plpgsql as $$
    declare
        trec	record;
    begin
        for trec in select username from base.priv_v where priv = rname and level = 0 and username is not null loop
            execute 'grant "' || rname || '_0" to ' || trec.username;
        end loop;
    end;
$$;
create trigger base_priv_tr_ad before delete on base.priv for each row execute procedure base.priv_tf_dgrp();
create trigger base_priv_tr_iugrp before insert or update on base.priv for each row execute procedure base.priv_tf_iugrp();
create trigger base_token_tr_seq before insert on base.token for each row execute procedure base.token_tf_seq();
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
create function base.validate_token(uname text, tok text, pub text) returns boolean language plpgsql as $$
    declare
      trec	record;
    begin
      select into trec * from base.token_v where username = uname order by token_seq desc limit 1;
      if found and trec.valid and tok = trec.token and trec.allows = 'login' then
        update base.token set used = current_timestamp where token_ent = trec.token_ent and token_seq = trec.token_seq;
        update base.ent set conn_pub = pub where id = trec.token_ent;
        return true;
      end if;
      return false;
    end;
$$;
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
create view json.user as select
    id		as "id"
  , peer_cdi	as "cdi"
  , ent_name	as "name"
  , ent_type	as "type"
  , fir_name	as "first"
  , mid_name	as "middle"
  , pref_name	as "prefer"
  , born_date	as "begin"
  , country	as "juris"
  , tax_id	as "taxid"
    from mychips.users_v where not user_ent is null with cascaded check option;
create function mychips.chits_tf_seq() returns trigger language plpgsql security definer as $$
    begin
        if new.chit_idx is null then
            select into new.chit_idx coalesce(max(chit_idx),0)+1 from mychips.chits where chit_ent = new.chit_ent and chit_seq = new.chit_seq;
        end if;
        return new;
    end;
$$;
create trigger mychips_chits_tr_cache after insert or update or delete on mychips.chits for each row execute procedure mychips.chits_tf_cache();
create trigger mychips_chits_tr_change after insert or update or delete on mychips.chits for each statement execute procedure mychips.change_tf_notify('chits');
create index mychips_chits_x_chit_date on mychips.chits (chit_date);
create index mychips_chits_x_chit_guid on mychips.chits (chit_guid);
create index mychips_chits_x_chit_type on mychips.chits (chit_type);
create function mychips.confirms_tf_seq() returns trigger language plpgsql security definer as $$
    begin
        if new.conf_idx is null then
            select into new.conf_idx coalesce(max(conf_idx),0)+1 from mychips.confirms where conf_ent = new.conf_ent and conf_seq = new.conf_seq;
        end if;
        return new;
    end;
$$;
create trigger mychips_contracts_tr_bi before insert on mychips.contracts for each row execute procedure mychips.contracts_tf_bi();
create trigger mychips_contracts_tr_bu before update on mychips.contracts for each row execute procedure mychips.contracts_tf_bu();
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
create function mychips.internal_lift(units bigint, uupath uuid[]) returns boolean language plpgsql security definer as $$
    declare
      tally_id	uuid;
      lift_id	uuid;
      trec	record;
      tcount	int;
    begin
      lift_id = uuid_generate_v1();

      foreach tally_id in array uupath loop
        tcount = 0;
        for trec in select * from mychips.tallies where tally_guid = tally_id order by tally_type loop
          insert into mychips.chits (chit_ent, chit_seq, chit_guid, chit_type, signature, units) values (trec.tally_ent, trec.tally_seq, lift_id, 'lift', 'Valid', -units);
          tcount = tcount + 1;
        end loop;
        if tcount != 2 then
          raise exception 'Could not find exactly two tallies for UUID:%', tally_id;
          return false;
        end if;
      end loop;
    return true;
    end;
$$;
create function mychips.lift_cycle(maxNum int default 1) returns jsonb language plpgsql security definer as $$
    declare
      status	jsonb = '{"done": 0}';
      prec	record;
      orders	text default 'bang desc';
      tstr	text;
      tarr	text[];
      oarr	text[];
      lift_id	uuid;
      min_units	int default base.parm('lifts','minimum');
      count	int default 0;
      rows	int;
    begin
      select into prec * from base.parm_v where module = 'lifts' and parm = 'order';
      if found then				-- Build a custom order-by clause
        foreach tstr in array regexp_split_to_array(prec.value, ',') loop
          oarr = regexp_split_to_array(btrim(tstr), E'\\s+');

          tarr = array_append(tarr, quote_ident(oarr[1]) || case when oarr[2] = 'desc' then ' desc' else '' end);
        end loop;
        orders = array_to_string(tarr, ', ');
      end if;


      while count < maxNum loop
        tstr = 'select id, length, min, max, cost, path, uuids from mychips.paths_v where circuit and min >= $1 order by ' || orders || ' limit 1';

        execute tstr into prec using min_units;
        get diagnostics rows = ROW_COUNT;

        if rows < 1 then exit; end if;
        if not mychips.internal_lift(prec.min, prec.uuids) then exit; end if;
        count = count + 1;
      end loop;
    return jsonb_set(status, '{done}', count::text::jsonb);
    end;
$$;
create function mychips.peer_sock(text) returns text stable language sql as $$
    select peer_sock from mychips.peers_v where id = $1;
$$;
create view mychips.peers_v_flat as select 
    p.*
  , a.bill_addr, a.bill_city, a.bill_state, a.bill_pcode, a.bill_country
  , a.ship_addr, a.ship_city, a.ship_state, a.ship_pcode, a.ship_country
  , c.phone_comm, c.cell_comm, c.email_comm, c.web_comm

    from	mychips.peers_v		p
    left join	base.addr_v_flat	a on a.id = p.id
    left join	base.comm_v_flat	c on c.id = p.id;
create function mychips.peers_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    if exists (select id from base.ent where id = new.id) then	-- if primary table record already exists
        update base.ent set mod_by = session_user,mod_date = current_timestamp where id = new.id;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.ent';

        execute 'select ' || str || ';' into trec using new;
        insert into base.ent (ent_name,ent_type,ent_cmt,fir_name,mid_name,pref_name,title,gender,marital,born_date,username,ent_inact,country,tax_id,bank,proxy,mod_by,mod_date) values (trec.ent_name,trec.ent_type,trec.ent_cmt,trec.fir_name,trec.mid_name,trec.pref_name,trec.title,trec.gender,trec.marital,trec.born_date,trec.username,trec.ent_inact,trec.country,trec.tax_id,trec.bank,trec.proxy,session_user,current_timestamp) returning id into new.id;
    end if;
    
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.peers';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.peers (peer_ent,peer_cdi,peer_hid,peer_pub,peer_inet,peer_port,peer_cmt) values (new.id,trec.peer_cdi,trec.peer_hid,trec.peer_pub,trec.peer_inet,trec.peer_port,trec.peer_cmt);
    select into new * from mychips.peers_v where id = new.id;
    return new;
  end;
$$;
create function mychips.peers_v_updfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    update base.ent set ent_name = new.ent_name,ent_cmt = new.ent_cmt,fir_name = new.fir_name,mid_name = new.mid_name,pref_name = new.pref_name,title = new.title,gender = new.gender,marital = new.marital,born_date = new.born_date,ent_inact = new.ent_inact,country = new.country,tax_id = new.tax_id,bank = new.bank,proxy = new.proxy,mod_by = session_user,mod_date = current_timestamp where id = old.id returning id into new.id;
    
    
    if exists (select peer_ent from mychips.peers where peer_ent = old.peer_ent) then				-- if primary table record already exists
        update mychips.peers set peer_cdi = new.peer_cdi,peer_hid = new.peer_hid,peer_pub = new.peer_pub,peer_inet = new.peer_inet,peer_port = new.peer_port,peer_cmt = new.peer_cmt,mod_by = session_user,mod_date = current_timestamp where peer_ent = old.peer_ent;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.peers';

        execute 'select ' || str || ';' into trec using new;
        insert into mychips.peers (peer_cdi,peer_hid,peer_pub,peer_inet,peer_port,peer_cmt,mod_by,mod_date) values (trec.peer_cdi,trec.peer_hid,trec.peer_pub,trec.peer_inet,trec.peer_port,trec.peer_cmt,session_user,current_timestamp);
    end if;

    select into new * from mychips.peers_v where id = new.id;
    return new;
  end;
$$;
create trigger mychips_tallies_tr_seq before insert on mychips.tallies for each row execute procedure mychips.tallies_tf_seq();
create view mychips.tallies_v as select 
    te.tally_ent, te.tally_seq, te.request, te.comment, te.cr_limit, te.dr_limit, te.tally_guid, te.tally_type, te.version, te.partner, te.contract, te.crt_by, te.mod_by, te.crt_date, te.mod_date, te.tally_date, te.status, te.units_c
  , ue.peer_cdi		as user_cdi
  , ue.peer_sock	as user_sock
  , ue.std_name		as user_name
  , te.user_sig
  , pe.peer_cdi		as part_cdi
  , pe.peer_sock	as part_sock
  , pe.std_name		as part_name
  , te.part_sig
  , mychips.tally_state(status,request,user_sig,part_sig,units_c) as state
  , mychips.tally_state(status,request,user_sig,part_sig,units_c) = any(array['peerProffer','closing']) as action
  , jsonb_build_object(
       'guid', te.tally_guid,
       'version', te.version,
       'stock', case when te.tally_type = 'stock' then ue.peer_cdi else pe.peer_cdi end,
       'foil',  case when te.tally_type = 'stock' then pe.peer_cdi else ue.peer_cdi end,
       'created', te.tally_date,
       'contract', te.contract,
       'signed', json_build_object(
         'digest', '',
         'stock', case when te.tally_type = 'stock' then te.user_sig else te.part_sig end,
         'foil',  case when te.tally_type = 'stock' then te.part_sig else te.user_sig end
       )
    )			as json
  , coalesce(tc.units,0)			as units
  , te.units_c::float8 / case when te.tally_type = 'stock' then 1000.00 else -1000.00 end		as total_c
  , coalesce(tc.units,0)::float8 / case when te.tally_type = 'stock' then 1000.00 else -1000.00 end	as total
  , coalesce(tc.chits,0)			as chits

    from	mychips.tallies	te
    join	mychips.users_v	ue on ue.user_ent = te.tally_ent
    join	mychips.users_v	pe on pe.user_ent = te.partner
    left join	(select chit_ent, chit_seq, sum(units) as units, count(chit_idx) as chits from mychips.chits group by 1,2) tc on tc.chit_ent = te.tally_ent and tc.chit_seq = te.tally_seq
    











;
create function mychips.tally_notices() returns void language plpgsql as $$
    declare
        trec		record;
    begin
        for trec in select * from mychips.tallies where request is not null loop
            perform mychips.tally_notify(trec);
        end loop;
        for trec in select * from mychips.chits where request is not null loop
            perform mychips.chit_notify(trec);
        end loop;
    end;
$$;
create view mychips.tokens_v as select t.token_ent, t.token_seq, t.allows, t.token, t.token_cmt, t.used, t.exp_date, t.crt_by, t.mod_by, t.crt_date, t.mod_date
      , u.peer_cdi, u.user_inet, u.user_port, u.std_name
      , t.exp_date <= current_timestamp as "expired"
      , t.exp_date > current_timestamp and not used as "valid"

    from	mychips.tokens	t
    join	mychips.users_v	u	on u.user_ent = t.token_ent

    ;
    ;
    create rule mychips_tokens_v_delete as on delete to mychips.tokens_v
        do instead delete from mychips.tokens where token_ent = old.token_ent and token_seq = old.token_seq;
create trigger mychips_token_tr_seq before insert on mychips.tokens for each row execute procedure mychips.token_tf_seq();
create view mychips.users_v_flat as select 
    u.*
  , a.bill_addr, a.bill_city, a.bill_state, a.bill_pcode, a.bill_country
  , a.ship_addr, a.ship_city, a.ship_state, a.ship_pcode, a.ship_country
  , c.phone_comm, c.cell_comm, c.email_comm, c.web_comm

    from	mychips.users_v		u
    left join	base.addr_v_flat	a on a.id = u.id
    left join	base.comm_v_flat	c on c.id = u.id;
create function mychips.users_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    if exists (select id from base.ent where id = new.id) then	-- if primary table record already exists
        update base.ent set mod_by = session_user,mod_date = current_timestamp where id = new.id;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.ent';

        execute 'select ' || str || ';' into trec using new;
        insert into base.ent (ent_name,ent_type,ent_cmt,fir_name,mid_name,pref_name,title,gender,marital,born_date,username,ent_inact,country,tax_id,bank,proxy,mod_by,mod_date) values (trec.ent_name,trec.ent_type,trec.ent_cmt,trec.fir_name,trec.mid_name,trec.pref_name,trec.title,trec.gender,trec.marital,trec.born_date,trec.username,trec.ent_inact,trec.country,trec.tax_id,trec.bank,trec.proxy,session_user,current_timestamp) returning id into new.id;
    end if;
    
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.peers';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.peers (peer_ent,peer_cdi,peer_hid,peer_pub,peer_inet,peer_port,peer_cmt) values (new.id,trec.peer_cdi,trec.peer_hid,trec.peer_pub,trec.peer_inet,trec.peer_port,trec.peer_cmt);
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.users';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.users (user_ent,user_inet,user_port,user_stat,user_cmt,host_id) values (new.id,trec.user_inet,trec.user_port,trec.user_stat,trec.user_cmt,trec.host_id);
    select into new * from mychips.users_v where id = new.id;
    return new;
  end;
$$;
create function mychips.users_v_updfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    update base.ent set ent_name = new.ent_name,ent_cmt = new.ent_cmt,fir_name = new.fir_name,mid_name = new.mid_name,pref_name = new.pref_name,title = new.title,gender = new.gender,marital = new.marital,born_date = new.born_date,ent_inact = new.ent_inact,country = new.country,tax_id = new.tax_id,bank = new.bank,proxy = new.proxy,mod_by = session_user,mod_date = current_timestamp where id = old.id returning id into new.id;
    
    
    if exists (select peer_ent from mychips.peers where peer_ent = old.peer_ent) then				-- if primary table record already exists
        update mychips.peers set peer_cdi = new.peer_cdi,peer_hid = new.peer_hid,peer_pub = new.peer_pub,peer_inet = new.peer_inet,peer_port = new.peer_port,peer_cmt = new.peer_cmt,mod_by = session_user,mod_date = current_timestamp where peer_ent = old.peer_ent;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.peers';

        execute 'select ' || str || ';' into trec using new;
        insert into mychips.peers (peer_cdi,peer_hid,peer_pub,peer_inet,peer_port,peer_cmt,mod_by,mod_date) values (trec.peer_cdi,trec.peer_hid,trec.peer_pub,trec.peer_inet,trec.peer_port,trec.peer_cmt,session_user,current_timestamp);
    end if;

    
    if exists (select user_ent from mychips.users where user_ent = old.user_ent) then				-- if primary table record already exists
        update mychips.users set user_inet = new.user_inet,user_port = new.user_port,user_stat = new.user_stat,user_cmt = new.user_cmt,host_id = new.host_id,mod_by = session_user,mod_date = current_timestamp where user_ent = old.user_ent;
    else
        execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.users';

        execute 'select ' || str || ';' into trec using new;
        insert into mychips.users (user_inet,user_port,user_stat,user_cmt,host_id,mod_by,mod_date) values (trec.user_inet,trec.user_port,trec.user_stat,trec.user_cmt,trec.host_id,session_user,current_timestamp);
    end if;

    select into new * from mychips.users_v where id = new.id;
    return new;
  end;
$$;
create trigger wylib_data_tr_notify after insert or update or delete on wylib.data for each row execute procedure wylib.data_tf_notify();
create view wylib.data_v as select wd.ruid, wd.component, wd.name, wd.descr, wd.access, wd.data, wd.owner, wd.crt_by, wd.mod_by, wd.crt_date, wd.mod_date
      , oe.std_name		as own_name

    from	wylib.data	wd
    join	base.ent_v	oe	on oe.id = wd.owner
    where	access = 'read' or owner = base.curr_eid();
create function base.addr_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'base.addr_v';
    execute 'select ' || str || ';' into trec using new;
    insert into base.addr (addr_ent,addr_spec,city,state,pcode,country,addr_cmt,addr_type,addr_prim,addr_inact,crt_by,mod_by,crt_date,mod_date) values (new.addr_ent,trec.addr_spec,trec.city,trec.state,trec.pcode,trec.country,trec.addr_cmt,trec.addr_type,trec.addr_prim,trec.addr_inact,session_user,session_user,current_timestamp,current_timestamp) returning addr_ent,addr_seq into new.addr_ent, new.addr_seq;
    select into new * from base.addr_v where addr_ent = new.addr_ent and addr_seq = new.addr_seq;
    return new;
  end;
$$;
create function base.addr_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.addr set addr_spec = new.addr_spec,city = new.city,state = new.state,pcode = new.pcode,country = new.country,addr_cmt = new.addr_cmt,addr_type = new.addr_type,addr_prim = new.addr_prim,addr_inact = new.addr_inact,mod_by = session_user,mod_date = current_timestamp where addr_ent = old.addr_ent and addr_seq = old.addr_seq returning addr_ent,addr_seq into new.addr_ent, new.addr_seq;
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
    insert into base.comm (comm_ent,comm_type,comm_spec,comm_cmt,comm_inact,comm_prim,crt_by,mod_by,crt_date,mod_date) values (new.comm_ent,trec.comm_type,trec.comm_spec,trec.comm_cmt,trec.comm_inact,trec.comm_prim,session_user,session_user,current_timestamp,current_timestamp) returning comm_ent,comm_seq into new.comm_ent, new.comm_seq;
    select into new * from base.comm_v where comm_ent = new.comm_ent and comm_seq = new.comm_seq;
    return new;
  end;
$$;
create function base.comm_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update base.comm set comm_type = new.comm_type,comm_spec = new.comm_spec,comm_cmt = new.comm_cmt,comm_inact = new.comm_inact,comm_prim = new.comm_prim,mod_by = session_user,mod_date = current_timestamp where comm_ent = old.comm_ent and comm_seq = old.comm_seq returning comm_ent,comm_seq into new.comm_ent, new.comm_seq;
    select into new * from base.comm_v where comm_ent = new.comm_ent and comm_seq = new.comm_seq;
    return new;
  end;
$$;
create trigger base_parm_audit_tr_bi before insert on base.parm_audit for each row execute procedure base.parm_audit_tf_bi();
create trigger base_parm_tr_audit_d after delete on base.parm for each row execute procedure base.parm_tf_audit_d();
create trigger base_parm_tr_audit_u after update on base.parm for each row execute procedure base.parm_tf_audit_u();
create trigger base_parm_v_tr_del instead of delete on base.parm_v for each row execute procedure base.parm_v_tf_del();
create trigger base_parm_v_tr_ins instead of insert on base.parm_v for each row execute procedure base.parm_v_tf_ins();
create trigger base_parm_v_tr_upd instead of update on base.parm_v for each row execute procedure base.parm_v_tf_upd();
create trigger base_token_v_tr_ins instead of insert on base.token_v for each row execute procedure base.token_v_insfunc();
create view json.address as select
    addr_ent	as "id"
  , addr_seq	as "seq"
  , addr_spec	as "spec"
  , addr_type	as "type"
  , addr_prim	as "main"
  , city	as "locale"
  , state	as "state"
  , pcode	as "post"
  , addr_cmt	as "comment"
  , addr_inact	as "prior"
    from base.addr_v where not addr_ent is null with cascaded check option;
create view json.connect as select
    comm_ent	as "id"
  , comm_seq	as "seq"
  , comm_spec	as "spec"
  , comm_type	as "media"
  , comm_cmt	as "comment"
  , comm_inact	as "prior"
    from base.comm_v where not comm_ent is null with cascaded check option;
create view json.tally as select
    tally_ent		as "id"
  , tally_guid		as "guid"
  , version		as "version"
  , case when tally_type = 'stock' then user_cdi else part_cdi end as "stock"
  , case when tally_type = 'stock' then part_cdi else user_cdi end as "foil"
  , tally_date		as "created"
  , contract		as "contract"

    from	mychips.tallies_v;
create trigger mychips_chits_tr_seq before insert on mychips.chits for each row execute procedure mychips.chits_tf_seq();
create view mychips.chits_v as select 
    ch.chit_ent, ch.chit_seq, ch.chit_idx, ch.request, ch.signature, ch.units, ch.pro_quo, ch.memo, ch.chit_guid, ch.chit_type, ch.crt_by, ch.mod_by, ch.crt_date, ch.mod_date, ch.chit_date
  , te.user_cdi
  , te.part_cdi
  , te.tally_type
  , case when te.tally_type = 'stock' and ch.units >= 0 or te.tally_type = 'foil' and ch.units < 0 then 'debit' else 'credit' end		as effect
         
  , ch.units::float8 / 1000.00	as value
  , ch.units::float8 * case when te.tally_type = 'stock' then 1 else -1 end / 1000	as amount
  , mychips.chit_state(te.tally_type = 'stock' and ch.units >= 0 or te.tally_type = 'foil' and ch.units < 0, ch.request, ch.signature)	as state
  , mychips.chit_state(te.tally_type = 'stock' and ch.units >= 0 or te.tally_type = 'foil' and ch.units < 0, ch.request, ch.signature) = any(array['peerInvoice','peerDecline']) as action
  , jsonb_build_object(
       'guid',		ch.chit_guid,
       'type',		ch.chit_type,
       'date',		ch.chit_date,
       'units',		ch.units,
       'signed',	ch.signature
  )						as json
    from	mychips.chits		ch
    join	mychips.tallies_v	te on te.tally_ent = ch.chit_ent and te.tally_seq = ch.chit_seq;
create trigger mychips_confirms_tr_seq before insert on mychips.confirms for each row execute procedure mychips.confirms_tf_seq();
create trigger mychips_contracts_v_tr_ins instead of insert on mychips.contracts_v for each row execute procedure mychips.contracts_v_insfunc();
create trigger mychips_contracts_v_tr_upd instead of update on mychips.contracts_v for each row execute procedure mychips.contracts_v_updfunc();
create trigger mychips_peers_v_tr_ins instead of insert on mychips.peers_v for each row execute procedure mychips.peers_v_insfunc();
create trigger mychips_peers_v_tr_upd instead of update on mychips.peers_v for each row execute procedure mychips.peers_v_updfunc();
create view mychips.tallies_v_sum as select 
    tally_ent
  , count(tally_seq)	as tallies
  , sum(total_c)	as total_c
  , sum(total)		as total
  , sum(case when tally_type = 'stock' then total_c else 0 end)	as stock_total_c
  , sum(case when tally_type = 'stock' then total else 0 end)	as stock_total
  , sum(case when tally_type = 'foil' then total_c else 0 end)	as foil_total_c
  , sum(case when tally_type = 'foil' then total else 0 end)	as foil_total
  , count(nullif(tally_type, 'foil'))	as stocks
  , count(nullif(tally_type, 'stock'))	as foils
  , array_agg(partner)	as partners
  , array_agg(partner) filter (where tally_type = 'stock')	as clients
  , array_agg(partner) filter (where tally_type = 'foil')	as vendors
  from mychips.tallies_v group by 1;
create function mychips.tally_notify(tally mychips.tallies) returns boolean language plpgsql security definer as $$
    declare
        act	text;
        jrec	jsonb = '{"target": "tally"}';
        urec	record;
        prec	record;
        channel	text = 'mychips_peer';
    begin
        if tally.status = 'void'  and tally.request = 'draft' then
            act = 'userDraft';
        elsif tally.status = 'draft' and tally.request = 'void'  then
            act = 'userVoid';
        elsif tally.status = 'draft' and tally.request = 'open'  then
            act = 'userAccept';
        elsif tally.status = 'open'  and tally.request = 'close' then
            act = 'userClose';
        end if;
        if act is null then return false; end if;


        select into urec peer_cdi, host_id from mychips.users_v where user_ent = tally.tally_ent;
        select into prec peer_cdi, peer_sock from mychips.peers_v where peer_ent = tally.partner;
        if not urec.host_id is null then
            channel = channel || '_' || urec.host_id;
        end if;

        jrec = jsonb_set(jrec, '{peer}', to_jsonb(prec.peer_cdi));
        jrec = jsonb_set(jrec, '{user}', to_jsonb(urec.peer_cdi));
        jrec = jsonb_set(jrec, '{entity}', to_jsonb(tally.tally_ent));
        jrec = jsonb_set(jrec, '{action}', to_jsonb(act));
        jrec = jsonb_set(jrec, '{at}', to_jsonb(prec.peer_sock));
        jrec = jsonb_set(jrec, '{object}', (select json from mychips.tallies_v where tally_ent = tally.tally_ent and tally_seq = tally.tally_seq));
raise notice 'Tally notice:%', jrec::text;
        perform pg_notify(channel, jrec::text);
        return true;
    end;
$$;
create function mychips.tally_process(msg jsonb, recipe jsonb) returns text language plpgsql as $$
    declare
        cdi		text = msg->>'user';
        obj		jsonb = msg->'object';
        entity		text;
        guid		uuid = obj->>'guid';
        curState	text;
        lrec		record;
        trec		record;
        tallyType text; notType text; partner text;
    begin

            select into entity peer_ent from mychips.peers where peer_cdi = cdi;
            if not found then return null; end if;


        select into trec tally_ent, tally_seq, state from mychips.tallies_v where tally_ent = entity and tally_guid = guid;
        curState = trec.state;

        if not found then
            curState = 'null';
        end if;
        if not (jsonb_build_array(curState) <@ (recipe->'context')) then	--Not in any applicable state

            return curState;
        end if;

        if recipe ? 'upsert' then

          tallyType = (case when obj->>'stock' = cdi then 'stock' else 'foil' end);
          notType = (case when obj->>'stock' = cdi then 'foil' else 'stock' end);

          if curState = 'null' then			-- Need to do insert
            select into partner peer_ent from mychips.peers where peer_cdi = case when tallyType = 'stock' then obj->>'foil' else obj->>'stock' end;
            if not found then return null; end if;
            
            execute 'insert into mychips.tallies (tally_ent,tally_guid,tally_type,tally_date,version,partner,contract,status,comment,user_sig,part_sig,cr_limit,dr_limit) values ($1,$2,$3,current_timestamp,$4,$5,$6,$7,$8,$9,$10,$11,$12) returning tally_ent, tally_seq' into trec
                using entity, guid, tallyType, (obj->>'version')::int, partner, obj->'contract', 'draft', obj->'comment', obj->'signed'->>tallyType, obj->'signed'->>notType, coalesce((obj->>'crLimit')::bigint,0), coalesce((obj->>'drLimit')::bigint,0);
          else						-- Tally already exists, do update
            execute 'update mychips.tallies set version = $1, contract = $2, status = $3, comment = $4, user_sig = $5, part_sig = $6, cr_limit = $7, dr_limit = $8 where tally_ent = $9 and tally_seq = $10'
                using (obj->>'version')::int, obj->'contract', 'draft', obj->'comment', obj->'signed'->>tallyType, obj->'signed'->>notType, coalesce((obj->>'crLimit')::bigint,0), coalesce((obj->>'drLimit')::bigint,0), trec.tally_ent, trec.tally_seq;
          end if;
        end if;

        if recipe ? 'update' then
          for lrec in select * from jsonb_each_text(recipe->'update') loop	--Fixme: should probably restrict which columns can be updated by this method

            execute 'update mychips.tallies set request = null, ' || lrec.key || ' = $1 where tally_ent = $2 and tally_seq = $3' using lrec.value, trec.tally_ent, trec.tally_seq;
          end loop;
          update mychips.tallies set request = null where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
        end if;


        select into trec tally_ent,tally_seq,state,action,json from mychips.tallies_v where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
        if trec.action or (trec.state = 'open' and curState is distinct from 'open') then	-- Also notify if changed to open status
raise notice '  tally notify for user %', trec.tally_ent;
            perform pg_notify('mychips_admin', trec.json::text);
            perform pg_notify('mychips_user_'||trec.tally_ent::text, trec.json::text);
        end if;
        return trec.state;
    end;
$$;
create view mychips.tickets_v as select
    u.id		as "id"
  , t.token_seq
  , case when t.allows = 'user' then u.user_sock else u.peer_cdi end		as "url"
  , t.token
  , s.peer_pub
  , t.exp_date
  , json_build_object('url', case when t.allows = 'user' then u.user_sock else u.peer_cdi end, 'token', t.token, 'expires', t.exp_date) as "json"

    from	mychips.users_v	u
    join	mychips.tokens	t on t.token_ent = u.id
    left join	base.parm	p on p.module = 'mychips' and p.parm = 'site_ent'
    left join	mychips.peers	s on s.peer_ent = p.v_text
    where	t.exp_date > current_timestamp and not t.used;
create function mychips.tokens_v_insfunc() returns trigger language plpgsql security definer as $$
  declare
    trec record;
    str  varchar;
  begin
    execute 'select string_agg(val,'','') from wm.column_def where obj = $1;' into str using 'mychips.tokens_v';
    execute 'select ' || str || ';' into trec using new;
    insert into mychips.tokens (token_ent,token_seq,allows,token,token_cmt,used,exp_date,crt_by,mod_by,crt_date,mod_date) values (new.token_ent,new.token_seq,trec.allows,trec.token,trec.token_cmt,trec.used,trec.exp_date,session_user,session_user,current_timestamp,current_timestamp) returning token_ent,token_seq into new.token_ent, new.token_seq;
    select into new * from mychips.tokens_v where token_ent = new.token_ent and token_seq = new.token_seq;
    return new;
  end;
$$;
create function mychips.tokens_v_updfunc() returns trigger language plpgsql security definer as $$
  begin
    update mychips.tokens set allows = new.allows,token = new.token,token_cmt = new.token_cmt,used = new.used,exp_date = new.exp_date,mod_by = session_user,mod_date = current_timestamp where token_ent = old.token_ent and token_seq = old.token_seq returning token_ent,token_seq into new.token_ent, new.token_seq;
    select into new * from mychips.tokens_v where token_ent = new.token_ent and token_seq = new.token_seq;
    return new;
  end;
$$;
create trigger mychips_users_v_tr_ins instead of insert on mychips.users_v for each row execute procedure mychips.users_v_insfunc();
create trigger mychips_users_v_tr_upd instead of update on mychips.users_v for each row execute procedure mychips.users_v_updfunc();
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
create function wylib.set_data(comp text, nam text, des text, own int, dat jsonb) returns int language plpgsql as $$
    declare
      userid	int = coalesce(own, base.curr_eid());
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
create view json.ticket as select
    id			as "id"
  , token_seq		as "seq"
  , url			as "url"
  , token		as "token"
  , peer_pub		as "public"
  , exp_date		as "expires"
    from	mychips.tickets_v;
create view json.users as select
  cdi, name, type, first, middle, prefer, begin, juris, taxid
  , (select array_agg(to_jsonb(d)) from (select spec,type,main,locale,state,post,comment,prior from json.address a where a.id = id order by seq) d) as addresses
  , (select array_agg(to_jsonb(d)) from (select spec,media,comment,prior from json.connect c where c.id = id order by seq) d) as connects
    from json.user;
create function mychips.chit_notify(chit mychips.chits) returns boolean language plpgsql security definer as $$
    declare
        act	text	= chit.request;
        jrec	jsonb	= '{"target": "chit"}';
        channel	text	= 'mychips_peer';
        trec	record;
        urec	record;
    begin
        if act is null then return false; end if;
        
        select into trec * from mychips.tallies_v where tally_ent = chit.chit_ent and tally_seq = chit.chit_seq;
        select into urec host_id from mychips.users_v where user_ent = chit.chit_ent;
        if not urec.host_id is null then
            channel = channel || '_' || urec.host_id;
        end if;
        jrec = jsonb_set(jrec, '{peer}', to_jsonb(trec.part_cdi));
        jrec = jsonb_set(jrec, '{user}', to_jsonb(trec.user_cdi));
        jrec = jsonb_set(jrec, '{entity}', to_jsonb(chit.chit_ent));
        jrec = jsonb_set(jrec, '{tally}', to_jsonb(trec.tally_guid));
        jrec = jsonb_set(jrec, '{action}', to_jsonb(act));
        jrec = jsonb_set(jrec, '{at}', to_jsonb(trec.part_sock));
        jrec = jsonb_set(jrec, '{object}', (select json from mychips.chits_v where chit_ent = chit.chit_ent and chit_seq = chit.chit_seq and chit_idx = chit.chit_idx));
raise notice 'Chit notice:% %', channel, jrec::text;
        perform pg_notify(channel, jrec::text);
        return true;
    end;
$$;
create function mychips.chit_process(msg jsonb, recipe jsonb) returns text language plpgsql as $$
    declare
        cdi		text	= msg->>'user';
        obj		jsonb	= msg->'object';
        entity		text;
        guid		uuid	= obj->>'guid';
        curState	text;
        crec		record;
        trec		record;
        lrec		record;
    begin

            select into entity peer_ent from mychips.peers where peer_cdi = cdi;
            if not found then return null; end if;


        select into crec chit_ent, chit_seq, chit_idx, state from mychips.chits_v where chit_ent = entity and chit_guid = guid;
        curState = crec.state;
raise notice 'Chit cdi:% entity:% state:% recipe:%', cdi, crec.chit_ent, curState, recipe;
        if not found then
            curState = 'null';
        end if;

        if not (jsonb_build_array(curState) <@ (recipe->'context')) then	--Not in any applicable state
raise notice 'Z:% C:%', jsonb_build_array(curState), recipe->'context';
            return curState;
        end if;

        if recipe ? 'upsert' then
raise notice '  upsert obj:% curState:%', obj, curState;
          if curState = 'null' then			-- Need to do insert
            select into trec * from mychips.tallies where tally_ent = entity and tally_guid = (msg->>'tally')::uuid;
            if not found then return null; end if;
            
            execute 'insert into mychips.chits (chit_ent,chit_seq,chit_guid,chit_type,chit_date,signature,units,pro_quo,memo) values ($1,$2,$3,$4,current_timestamp,$5,$6,$7,$8) returning chit_ent, chit_seq, chit_idx' into crec
                using trec.tally_ent, trec.tally_seq, guid, obj->>'type', obj->>'signed', (obj->>'units')::bigint, obj->>'link', obj->>'memo';
          else						-- Chit already exists, do update
            execute 'update mychips.chits set signature = $1, units = $2, pro_quo = $3, memo = $4, request = null where chit_ent = $5 and chit_seq = $6 and chit_idx = $7'
                using obj->>'signed', (obj->>'units')::bigint, obj->>'link', obj->>'memo', crec.chit_ent, crec.chit_seq, crec.chit_idx;
          end if;
        end if;

        if recipe ? 'update' then
          for lrec in select * from jsonb_each_text(recipe->'update') loop	--Fixme: should probably restrict which columns can be updated by this method
raise notice '  update set % = %', lrec.key, lrec.value;
            execute 'update mychips.chits set ' || lrec.key || ' = $1 where chit_ent = $2 and chit_seq = $3 and chit_idx = $4' using lrec.value, crec.chit_ent, crec.chit_seq, crec.chit_idx;
          end loop;
          update mychips.chits set request = null where chit_ent = crec.chit_ent and chit_seq = crec.chit_seq and chit_idx = crec.chit_idx;
        end if;

        select into crec chit_ent,chit_seq,chit_idx,state,action,json from mychips.chits_v where chit_ent = crec.chit_ent and chit_seq = crec.chit_seq and chit_idx = crec.chit_idx;
        if crec.action or (crec.state = 'peerValid' and (curState is distinct from 'peerValid')) then	-- Also notify if changed to valid status
raise notice '  chit notify for user %', crec.chit_ent;
            perform pg_notify('mychips_admin', crec.json::text);
            perform pg_notify('mychips_user_'||crec.chit_ent::text, crec.json::text);
        end if;
        return crec.state;
    end;
$$;
create function mychips.chits_tf_notify() returns trigger language plpgsql security definer as $$
    declare
        dirty	boolean default false;
    begin

        if TG_OP = 'INSERT' then
            dirty = true;
        elsif new.request is not null and new.request is distinct from old.request then
            dirty = true;
        end if;
        if dirty then perform mychips.chit_notify(new); end if;
        return new;
    end;
$$;
create function mychips.tallies_tf_notify() returns trigger language plpgsql security definer as $$
    declare
        dirty	boolean default false;
    begin
        if TG_OP = 'INSERT' then
            dirty = true;
        elsif new.request is not null and new.request is distinct from old.request then
            dirty = true;
        end if;
        if dirty then perform mychips.tally_notify(new); end if;
        return new;
    end;
$$;
create function mychips.ticket_user(uid text) returns jsonb language plpgsql as $$
    declare
      retval	jsonb;
    begin
      insert into mychips.tokens (token_ent, allows) values (uid, 'user');
      select into retval json from mychips.tickets_v where id = uid;
      return retval;
    end;
$$;
create trigger mychips_tokens_v_tr_ins instead of insert on mychips.tokens_v for each row execute procedure mychips.tokens_v_insfunc();
create trigger mychips_tokens_v_tr_upd instead of update on mychips.tokens_v for each row execute procedure mychips.tokens_v_updfunc();
create trigger wylib_data_v_tr_del instead of delete on wylib.data_v for each row execute procedure wylib.data_v_tf_del();
create trigger wylib_data_v_tr_ins instead of insert on wylib.data_v for each row execute procedure wylib.data_v_tf_ins();
create trigger wylib_data_v_tr_upd instead of update on wylib.data_v for each row execute procedure wylib.data_v_tf_upd();
create function json.import(data jsonb, keys jsonb default null) returns record language plpgsql as $$
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

      if jsonb_typeof(data) = 'array' then
        for tmpObject in select jsonb_array_elements(data) loop		-- Recursively call for each array element
          newRecord = json.import(tmpObject, keys);
        end loop;
        return newRecord;
      elsif jsonb_typeof(data) != 'object' then
          return null;
      end if;

      for tableName in select jsonb_object_keys(data) loop		-- For each record in toplevel object (normally just one)
        tmpObject = data->tableName;


        for tmpKey in select jsonb_object_keys(keys) loop		-- For any primary key values passed in from above
          tmpObject = jsonb_set(tmpObject, array[tmpkey], keys->tmpkey);

        end loop;

        select array_to_string(pkey,',') into primKeyList from wm.table_data where td_sch = 'json' and td_tab = tableName;
        if not found then
          continue;
        end if;
        select array_agg(cdt_col), string_agg(quote_ident(cdt_col),',') into fieldArray, fieldList from wm.column_data where cdt_sch = 'json' and cdt_tab = tableName;

        cmd = 'insert into json.' || quote_ident(tableName) || ' (' || fieldList || ') select ' || fieldList || ' from jsonb_populate_record(NULL::json.' || quote_ident(tableName) || ', $1) returning ' || primKeyList;

        execute cmd into newRecord using tmpObject;


        for tmpKey in select jsonb_object_keys(tmpObject) loop		-- Find any nested sub-objects that need to be inserted
          if not (tmpKey = any(fieldArray)) then

            perform json.import(tmpObject->tmpKey, to_jsonb(newRecord));
          end if;
        end loop;
      
      end loop;
      

      return newRecord;
    end;
$$;
create trigger mychips_chits_tr_notice after insert or update on mychips.chits for each row execute procedure mychips.chits_tf_notify();
create trigger mychips_tallies_tr_notice after insert or update on mychips.tallies for each row execute procedure mychips.tallies_tf_notify();

--Data Dictionary:
insert into wm.table_text (tt_sch,tt_tab,language,title,help) values
  ('wm','releases','eng','Releases','Tracks the version number of each public release of the database design'),
  ('wm','objects','eng','Objects','Keeps data on database tables, views, functions, etc. telling how to build or drop each object and how it relates to other objects in the database.'),
  ('wm','objects_v','eng','Rel Objects','An enhanced view of the object table, expanded by showing the full object specifier, and each separate release this version of the object belongs to'),
  ('wm','objects_v_depth','eng','Dep Objects','An enhanced view of the object table, expanded by showing the full object specifier, each separate release this version of the object belongs to, and the maximum depth it is along any path in the dependency tree.'),
  ('wm','depends_v','eng','Dependencies','A recursive view showing which database objects depend on (must be created after) other database objects.'),
  ('wm','table_style','eng','Table Styles','Contains style flags to tell the GUI how to render each table or view'),
  ('wm','column_style','eng','Column Styles','Contains style flags to tell the GUI how to render the columns of a table or view'),
  ('wm','table_text','eng','Table Text','Contains a description of each table in the system'),
  ('wm','column_text','eng','Column Text','Contains a description for each column of each table in the system'),
  ('wm','value_text','eng','Value Text','Contains a description for the values which certain columns may be set to.  Used only for columns that can be set to one of a finite set of values (like an enumerated type).'),
  ('wm','message_text','eng','Message Text','Contains messages in a particular language to describe an error, or a widget feature or button'),
  ('wm','column_native','eng','Native Columns','Contains cached information about the tables and their columns which various higher level view columns derive from.  To query this directly from the information schema is somewhat slow, so wyseman caches it here when building the schema for faster access.'),
  ('wm','table_data','eng','Table Data','Contains information from the system catalogs about views and tables in the system'),
  ('wm','table_pub','eng','Tables','Joins information about tables from the system catalogs with the text descriptions defined in wyseman'),
  ('wm','view_column_usage','eng','View Column Usage','A version of a similar view in the information schema but faster.  For each view, tells what underlying table and column the view column uses.'),
  ('wm','column_data','eng','Column Data','Contains information from the system catalogs about columns of tables in the system'),
  ('wm','column_def','eng','Column Default','A view used internally for initializing columns to their default value'),
  ('wm','column_istyle','eng','Column Styles','A view of the default display styles for table and view columns'),
  ('wm','column_lang','eng','Column language','A view of descriptive language data as it applies to the columns of tables and views'),
  ('wm','column_meta','eng','Column Metadata','A view of data about the use and display of the columns of tables and views'),
  ('wm','table_lang','eng','Table Language','A view of titles and descriptions of database tables/views'),
  ('wm','table_meta','eng','Table Metadata','A view of data about the use and display of tables and views'),
  ('wm','column_pub','eng','Columns','Joins information about table columns from the system catalogs with the text descriptions defined in wyseman'),
  ('wm','fkeys_data','eng','Keys Data','Includes data from the system catalogs about how key fields in a table point to key fields in a foreign table.  Each key group is described on a separate row.'),
  ('wm','fkeys_pub','eng','Keys','Public view to see foreign key relationships between views and tables and what their native underlying tables/columns are.  One row per key group.'),
  ('wm','fkey_data','eng','Key Data','Includes data from the system catalogs about how key fields in a table point to key fields in a foreign table.  Each separate key field is listed as a separate row.'),
  ('wm','fkey_pub','eng','Key Info','Public view to see foreign key relationships between views and tables and what their native underlying tables/columns are.  One row per key column.'),
  ('wm','role_members','eng','Role Members','Summarizes information from the system catalogs about members of various defined roles'),
  ('wm','column_ambig','eng','Ambiguous Columns','A view showing view and their columns for which no definitive native table and column can be found automatically'),
  ('wylib','data','eng','GUI Data','Configuration and preferences data accessed by Wylib view widgets'),
  ('wylib','data_v','eng','GUI Data','A view of configuration and preferences data accessed by Wylib view widgets'),
  ('wylib','data','fi','GUI Data','Wylib-näkymäkomponenttien käyttämät konfigurointi- ja asetustiedot'),
  ('base','addr','eng','Addresses','Addresses (home, mailing, etc.) pertaining to entities'),
  ('base','addr_v','eng','Addresses','A view of addresses (home, mailing, etc.) pertaining to entities, with additional derived fields'),
  ('base','addr_prim','eng','Primary Address','Internal table to track which address is the main one for each given type'),
  ('base','addr_v_flat','eng','Entities Flat','A flattened view of entities showing their primary standard addresses'),
  ('base','comm','eng','Communication','Communication points (phone, email, fax, etc.) for entities'),
  ('base','comm_v','eng','Communication','View of users'' communication points (phone, email, fax, etc.) with additional helpful fields'),
  ('base','comm_prim','eng','Primary Communication','Internal table to track which communication point is the main one for each given type'),
  ('base','comm_v_flat','eng','Entities Flat','A flattened view of entities showing their primary standard contact points'),
  ('base','country','eng','Countries','Contains standard ISO data about international countries'),
  ('base','ent','eng','Entities','Entities, which can be a person, a company or a group'),
  ('base','ent_v','eng','Entities','A view of Entities, which can be a person, a company or a group, plus additional derived fields'),
  ('base','ent_link','eng','Entity Links','Links to show how one entity (like an employee) is linked to another (like his company)'),
  ('base','ent_link_v','eng','Entity Links','A view showing links to show how one entity (like an employee) is linked to another (like his company), plus the derived names of the entities'),
  ('base','ent_audit','eng','Entities Auditing','Table tracking changes to the entities table'),
  ('base','language','eng','Languages','Contains standard ISO data about international language codes'),
  ('base','token','eng','Access Tokens','Stores access codes which allow users to connect for the first time'),
  ('base','token_v','eng','Tokens','A view of the access codes, which allow users to connect for the first time'),
  ('base','parm','eng','System Parameters','Contains parameter settings of several types for configuring and controlling various modules across the database'),
  ('base','parm_v','eng','Parameters','System parameters are stored in different tables depending on their data type (date, integer, etc.).  This view is a union of all the different type tables so all parameters can be viewed and updated in one place.  The value specified will have to be entered in a way that is compatible with the specified type so it can be stored natively in its correct data type.'),
  ('base','parm_audit','eng','Parameters Auditing','Table tracking changes to the parameters table'),
  ('base','priv','eng','Privileges','Privileges assigned to each system user'),
  ('base','priv_v','eng','Privileges','Privileges assigned to each entity'),
  ('mychips','contracts','eng','Contracts','Each record contains contract language to be included by reference in a MyCHIPs tally or a similar agreement'),
  ('mychips','contracts_v','eng','Contracts','Each record contains contract language to be included by reference in a MyCHIPs tally or a similar agreement.'),
  ('mychips','paths_v','eng','Tally Pathways','A view showing network pathways between entities, based on the tallies they have in place'),
  ('mychips','peers','eng','CHIP Peers','All entities who trade CHIPs using on this server.  Includes this server''s users and their peers.'),
  ('mychips','peers_v','eng','CHIP Peers','Entities who trade CHIPs on this server, and their peer entities.'),
  ('mychips','tallies','eng','Tallies','Contains an entry for each tally, which is a record of credit transactions between two trading partners.'),
  ('mychips','tallies_v','eng','Tallies','Standard view containing an entry for each tally, which is a record of credit transactions between two trading partners.'),
  ('mychips','chits','eng','Chits','Contains an entry for each transaction of credit flow in either direction between the parties to the tally.'),
  ('mychips','confirms','eng','Confirmations','Contains records evidencing each time the parties confirmed the present balance of their tally.'),
  ('mychips','users','eng','CHIP Users','Entities who have CHIP accounts on this server.'),
  ('mychips','users_v','eng','CHIP Users','Entities who have CHIP accounts on this server.'),
  ('mychips','users','fin','CHIP käyttäjät','Yksiköt, joilla on CHIP-tilejä tällä palvelimella'),
  ('mychips','users_v','fin','CHIP käytäjät näkymä','Yksiköt, joilla on CHIP-tilejä tällä palvelimella');

insert into wm.column_text (ct_sch,ct_tab,ct_col,language,title,help) values
  ('wm','releases','release','eng','Release','The integer number of the release, starting with 1.  The current number in this field always designates a work-in-progress.  The number prior indicates the last public release.'),
  ('wm','releases','crt_date','eng','Created','When this record was created.  Indicates when development started on this release (And the prior release was frozen).'),
  ('wm','releases','sver_1','eng','BS Version','Dummy column with a name indicating the version of these bootstrap tables (which can''t be managed by wyseman themselves).'),
  ('wm','objects','obj_typ','eng','Type','The object type, for example: table, function, trigger, etc.'),
  ('wm','objects','obj_nam','eng','Name','The schema and name of object as known within that schema'),
  ('wm','objects','obj_ver','eng','Version','A sequential integer showing how many times this object has been modified, as a part of an official release.  Changes to the current (working) release do not increment this number.'),
  ('wm','objects','checked','eng','Checked','This record has had its dependencies and consistency checked'),
  ('wm','objects','clean','eng','Clean','The object represented by this record is built and current according to this create script'),
  ('wm','objects','module','eng','Module','The name of a code module (package) this object belongs to'),
  ('wm','objects','mod_ver','eng','Mod Vers','The version of the code module, or package this object belongs to'),
  ('wm','objects','source','eng','Source','The basename of the external source code file this object was parsed from'),
  ('wm','objects','deps','eng','Depends','A list of un-expanded dependencies for this object, exactly as expressed in the source file'),
  ('wm','objects','ndeps','eng','Normal Deps','An expanded and normalized array of dependencies, guaranteed to exist in another record of the table'),
  ('wm','objects','grants','eng','Grants','The permission grants found, applicable to this object'),
  ('wm','objects','col_data','eng','Display','Switches found, expressing preferred display characteristics for columns, assuming this is a view or table object'),
  ('wm','objects','crt_sql','eng','Create','The SQL code to build this object'),
  ('wm','objects','drp_sql','eng','Drop','The SQL code to drop this object'),
  ('wm','objects','min_rel','eng','Minimum','The oldest release this version of this object belongs to'),
  ('wm','objects','max_rel','eng','Maximum','The latest release this version of this object belongs to'),
  ('wm','objects','crt_date','eng','Created','When this object record was first created'),
  ('wm','objects','mod_date','eng','Modified','When this object record was last modified'),
  ('wm','objects_v','object','eng','Object','Full type and name of this object'),
  ('wm','objects_v','release','eng','Release','A release this version of the object belongs to'),
  ('wm','objects_v_depth','depth','eng','Max Depth','The maximum depth of this object along any path in the dependency tree'),
  ('wm','depends_v','object','eng','Object','Full object type and name (type:name)'),
  ('wm','depends_v','od_typ','eng','Type','Function, view, table, etc'),
  ('wm','depends_v','od_nam','eng','Name','Schema and name of object as known within that schema'),
  ('wm','depends_v','od_release','eng','Release','The release this object belongs to'),
  ('wm','depends_v','cycle','eng','Cycle','Prevents the recursive view gets into an infinite loop'),
  ('wm','depends_v','depend','eng','Depends On','Another object that must be created before this object'),
  ('wm','depends_v','depth','eng','Depth','The depth of the dependency tree, when following this particular dependency back to the root.'),
  ('wm','depends_v','path','eng','Path','The path of the dependency tree above this object'),
  ('wm','depends_v','fpath','eng','Full Path','The full path of the dependency tree above this object (including this object).'),
  ('wm','table_style','ts_sch','eng','Schema Name','The schema for the table this style pertains to'),
  ('wm','table_style','ts_tab','eng','Table Name','The name of the table this style pertains to'),
  ('wm','table_style','sw_name','eng','Name','The name of the style being described'),
  ('wm','table_style','sw_value','eng','Value','The value for this particular style'),
  ('wm','table_style','inherit','eng','Inherit','The value for this style can propagate to derivative views'),
  ('wm','column_style','cs_sch','eng','Schema Name','The schema for the table this style pertains to'),
  ('wm','column_style','cs_tab','eng','Table Name','The name of the table containing the column this style pertains to'),
  ('wm','column_style','cs_col','eng','Column Name','The name of the column this style pertains to'),
  ('wm','column_style','sw_name','eng','Name','The name of the style being described'),
  ('wm','column_style','sw_value','eng','Value','The value for this particular style'),
  ('wm','table_text','tt_sch','eng','Schema Name','The schema this table belongs to'),
  ('wm','table_text','tt_tab','eng','Table Name','The name of the table being described'),
  ('wm','table_text','language','eng','Language','The language this description is in'),
  ('wm','table_text','title','eng','Title','A short title for the table'),
  ('wm','table_text','help','eng','Description','A longer description of what the table is used for'),
  ('wm','column_text','ct_sch','eng','Schema Name','The schema this column''s table belongs to'),
  ('wm','column_text','ct_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','column_text','ct_col','eng','Column Name','The name of the column being described'),
  ('wm','column_text','language','eng','Language','The language this description is in'),
  ('wm','column_text','title','eng','Title','A short title for the column'),
  ('wm','column_text','help','eng','Description','A longer description of what the column is used for'),
  ('wm','value_text','vt_sch','eng','Schema Name','The schema of the table the column belongs to'),
  ('wm','value_text','vt_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','value_text','vt_col','eng','Column Name','The name of the column whose values are being described'),
  ('wm','value_text','value','eng','Value','The name of the value being described'),
  ('wm','value_text','language','eng','Language','The language this description is in'),
  ('wm','value_text','title','eng','Title','A short title for the value'),
  ('wm','value_text','help','eng','Description','A longer description of what it means when the column is set to this value'),
  ('wm','message_text','mt_sch','eng','Schema Name','The schema of the table this message belongs to'),
  ('wm','message_text','mt_tab','eng','Table Name','The name of the table this message belongs to is in'),
  ('wm','message_text','code','eng','Code','A unique code referenced in the source code to evoke this message in the language of choice'),
  ('wm','message_text','language','eng','Language','The language this message is in'),
  ('wm','message_text','title','eng','Title','A short version for the message, or its alert'),
  ('wm','message_text','help','eng','Description','A longer, more descriptive version of the message'),
  ('wm','column_native','cnt_sch','eng','Schema Name','The schema of the table this column belongs to'),
  ('wm','column_native','cnt_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','column_native','cnt_col','eng','Column Name','The name of the column whose native source is being described'),
  ('wm','column_native','nat_sch','eng','Schema Name','The schema of the native table the column derives from'),
  ('wm','column_native','nat_tab','eng','Table Name','The name of the table the column natively derives from'),
  ('wm','column_native','nat_col','eng','Column Name','The name of the column in the native table from which the higher level column derives'),
  ('wm','column_native','nat_exp','eng','Explic Native','The information about the native table in this record has been defined explicitly in the schema description (not derived from the database system catalogs)'),
  ('wm','column_native','pkey','eng','Primary Key','Wyseman can often determine the "primary key" for views on its own from the database.  When it can''t, you have to define it explicitly in the schema.  This indicates that thiscolumn should be regarded as a primary key field when querying the view.'),
  ('wm','table_data','td_sch','eng','Schema Name','The schema the table is in'),
  ('wm','table_data','td_tab','eng','Table Name','The name of the table being described'),
  ('wm','table_data','tab_kind','eng','Kind','Tells whether the relation is a table or a view'),
  ('wm','table_data','has_pkey','eng','Has Pkey','Indicates whether the table has a primary key defined in the database'),
  ('wm','table_data','obj','eng','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','table_data','cols','eng','Columns','Indicates how many columns are in the table'),
  ('wm','table_data','system','eng','System','True if the table/view is built in to PostgreSQL'),
  ('wm','table_pub','sch','eng','Schema Name','The schema the table belongs to'),
  ('wm','table_pub','tab','eng','Table Name','The name of the table being described'),
  ('wm','table_pub','obj','eng','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','view_column_usage','view_catalog','eng','View Database','The database the view belongs to'),
  ('wm','view_column_usage','view_schema','eng','View Schema','The schema the view belongs to'),
  ('wm','view_column_usage','view_name','eng','View Name','The name of the view being described'),
  ('wm','view_column_usage','table_catalog','eng','Table Database','The database the underlying table belongs to'),
  ('wm','view_column_usage','table_schema','eng','Table Schema','The schema the underlying table belongs to'),
  ('wm','view_column_usage','table_name','eng','Table Name','The name of the underlying table'),
  ('wm','view_column_usage','column_name','eng','Column Name','The name of the column in the view'),
  ('wm','column_data','cdt_sch','eng','Schema Name','The schema of the table this column belongs to'),
  ('wm','column_data','cdt_tab','eng','Table Name','The name of the table this column is in'),
  ('wm','column_data','cdt_col','eng','Column Name','The name of the column whose data is being described'),
  ('wm','column_data','field','eng','Field','The number of the column as it appears in the table'),
  ('wm','column_data','nonull','eng','Not Null','Indicates that the column is not allowed to contain a null value'),
  ('wm','column_data','length','eng','Length','The normal number of characters this item would occupy'),
  ('wm','column_data','type','eng','Data Type','The kind of data this column holds, such as integer, string, date, etc.'),
  ('wm','column_data','def','eng','Default','Default value for this column if none is explicitly assigned'),
  ('wm','column_data','tab_kind','eng','Table/View','The kind of database relation this column is in (r=table, v=view)'),
  ('wm','column_data','is_pkey','eng','Def Prim Key','Indicates that this column is defined as a primary key in the database (can be overridden by a wyseman setting)'),
  ('wm','column_def','val','eng','Init Value','An expression used for default initialization'),
  ('wm','column_istyle','nat_value','eng','Native Style','The inherited style as specified by an ancestor object'),
  ('wm','column_istyle','cs_value','eng','Given Style','The style, specified explicitly for this object'),
  ('wm','column_istyle','cs_obj','eng','Object Name','The schema and table name this style applies to'),
  ('wm','column_lang','sch','eng','Schema','The schema that holds the table or view this language data applies to'),
  ('wm','column_lang','tab','eng','Table','The table or view this language data applies to'),
  ('wm','column_lang','obj','eng','Object','The schema name and the table/view name'),
  ('wm','column_lang','col','eng','Column','The name of the column the metadata applies to'),
  ('wm','column_lang','values','eng','Values','A JSON description of the allowable values for this column'),
  ('wm','column_lang','system','eng','System','Indicates if this table/view is built in to PostgreSQL'),
  ('wm','column_lang','nat','eng','Native','The (possibly ancestor) schema and table/view this language information descends from'),
  ('wm','column_meta','sch','eng','Schema','The schema that holds the table or view this metadata applies to'),
  ('wm','column_meta','tab','eng','Table','The table or view this metadata applies to'),
  ('wm','column_meta','obj','eng','Object','The schema name and the table/view name'),
  ('wm','column_meta','col','eng','Column','The name of the column the metadata applies to'),
  ('wm','column_meta','values','eng','Values','An array of allowable values for this column'),
  ('wm','column_meta','styles','eng','Styles','An array of default display styles for this column'),
  ('wm','column_meta','nat','eng','Native','The (possibly ancestor) schema and table/view this metadata descends from'),
  ('wm','table_lang','messages','eng','Messages','Human readable messages the computer may generate in connection with this table/view'),
  ('wm','table_lang','columns','eng','Columns','A JSON structure describing language information relevant to the columns in this table/view'),
  ('wm','table_lang','obj','eng','Object','The schema and table/view'),
  ('wm','table_meta','fkeys','eng','Foreign Keys','A JSON structure containing information about the foreign keys pointed to by this table'),
  ('wm','table_meta','obj','eng','Object','The schema and table/view'),
  ('wm','table_meta','pkey','eng','Primary Key','A JSON array describing the primary key fields for this table/view'),
  ('wm','table_meta','columns','eng','Columns','A JSON structure describing metadata information relevant to the columns in this table/view'),
  ('wm','column_pub','sch','eng','Schema Name','The schema of the table the column belongs to'),
  ('wm','column_pub','tab','eng','Table Name','The name of the table that holds the column being described'),
  ('wm','column_pub','col','eng','Column Name','The name of the column being described'),
  ('wm','column_pub','obj','eng','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','column_pub','nat','eng','Native Object','The name of the native table, prefixed by the native schema'),
  ('wm','column_pub','language','eng','Language','The language of the included textual descriptions'),
  ('wm','column_pub','title','eng','Title','A short title for the table'),
  ('wm','column_pub','help','eng','Description','A longer description of what the table is used for'),
  ('wm','fkeys_data','kst_sch','eng','Base Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkeys_data','kst_tab','eng','Base Table','The name of the table that has the referencing key fields'),
  ('wm','fkeys_data','kst_cols','eng','Base Columns','The name of the columns in the referencing table''s key'),
  ('wm','fkeys_data','ksf_sch','eng','Foreign Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkeys_data','ksf_tab','eng','Foreign Table','The name of the table that is referenced by the key fields'),
  ('wm','fkeys_data','ksf_cols','eng','Foreign Columns','The name of the columns in the referenced table''s key'),
  ('wm','fkeys_data','conname','eng','Constraint','The name of the the foreign key constraint in the database'),
  ('wm','fkeys_pub','tt_sch','eng','Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_tab','eng','Table','The name of the table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_cols','eng','Columns','The name of the columns in the referencing table''s key'),
  ('wm','fkeys_pub','tt_obj','eng','Object','Concatenated schema.table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_sch','eng','Nat Schema','The schema of the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_tab','eng','Nat Table','The name of the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_cols','eng','Nat Columns','The name of the columns in the native referencing table''s key'),
  ('wm','fkeys_pub','tn_obj','eng','Nat Object','Concatenated schema.table for the native table that has the referencing key fields'),
  ('wm','fkeys_pub','ft_sch','eng','For Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_tab','eng','For Table','The name of the table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_cols','eng','For Columns','The name of the columns referenced by the key'),
  ('wm','fkeys_pub','ft_obj','eng','For Object','Concatenated schema.table for the table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_sch','eng','For Nat Schema','The schema of the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_tab','eng','For Nat Table','The name of the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_cols','eng','For Nat Columns','The name of the columns in the native referenced by the key'),
  ('wm','fkeys_pub','fn_obj','eng','For Nat Object','Concatenated schema.table for the native table that is referenced by the key fields'),
  ('wm','fkey_data','kyt_sch','eng','Base Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkey_data','kyt_tab','eng','Base Table','The name of the table that has the referencing key fields'),
  ('wm','fkey_data','kyt_col','eng','Base Columns','The name of the column in the referencing table''s key'),
  ('wm','fkey_data','kyt_field','eng','Base Field','The number of the column in the referencing table''s key'),
  ('wm','fkey_data','kyf_sch','eng','Foreign Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkey_data','kyf_tab','eng','Foreign Table','The name of the table that is referenced by the key fields'),
  ('wm','fkey_data','kyf_col','eng','Foreign Columns','The name of the columns in the referenced table''s key'),
  ('wm','fkey_data','kyf_field','eng','Foreign Field','The number of the column in the referenced table''s key'),
  ('wm','fkey_data','key','eng','Key','The number of which field of a compound key this record describes'),
  ('wm','fkey_data','keys','eng','Keys','The total number of columns used for this foreign key'),
  ('wm','fkey_data','conname','eng','Constraint','The name of the the foreign key constraint in the database'),
  ('wm','fkey_pub','tt_sch','eng','Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkey_pub','tt_tab','eng','Table','The name of the table that has the referencing key fields'),
  ('wm','fkey_pub','tt_col','eng','Column','The name of the column in the referencing table''s key component'),
  ('wm','fkey_pub','tt_obj','eng','Object','Concatenated schema.table that has the referencing key fields'),
  ('wm','fkey_pub','tn_sch','eng','Nat Schema','The schema of the native table that has the referencing key fields'),
  ('wm','fkey_pub','tn_tab','eng','Nat Table','The name of the native table that has the referencing key fields'),
  ('wm','fkey_pub','tn_col','eng','Nat Column','The name of the column in the native referencing table''s key component'),
  ('wm','fkey_pub','tn_obj','eng','Nat Object','Concatenated schema.table for the native table that has the referencing key fields'),
  ('wm','fkey_pub','ft_sch','eng','For Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_tab','eng','For Table','The name of the table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_col','eng','For Column','The name of the column referenced by the key component'),
  ('wm','fkey_pub','ft_obj','eng','For Object','Concatenated schema.table for the table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_sch','eng','For Nat Schema','The schema of the native table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_tab','eng','For Nat Table','The name of the native table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_col','eng','For Nat Column','The name of the column in the native referenced by the key component'),
  ('wm','fkey_pub','fn_obj','eng','For Nat Object','Concatenated schema.table for the native table that is referenced by the key fields'),
  ('wm','fkey_pub','unikey','eng','Unikey','Used to differentiate between multiple fkeys pointing to the same destination, and multi-field fkeys pointing to multi-field destinations'),
  ('wm','role_members','role','eng','Role','The name of a role'),
  ('wm','role_members','member','eng','Member','The username of a member of the named role'),
  ('wm','column_ambig','sch','eng','Schema','The name of the schema this view is in'),
  ('wm','column_ambig','tab','eng','Table','The name of the view'),
  ('wm','column_ambig','col','eng','Column','The name of the column within the view'),
  ('wm','column_ambig','spec','eng','Specified','True if the definitive native table has been specified explicitly in the schema definition files'),
  ('wm','column_ambig','count','eng','Count','The number of possible native tables for this column'),
  ('wm','column_ambig','natives','eng','Natives','A list of the possible native tables for this column'),
  ('wylib','data','ruid','eng','Record ID','A unique ID number generated for each data record'),
  ('wylib','data','component','eng','Component','The part of the graphical, or other user interface that uses this data'),
  ('wylib','data','name','eng','Name','A name explaining the version or configuration this data represents (i.e. Default, Searching, Alphabetical, Urgent, Active, etc.)'),
  ('wylib','data','descr','eng','Description','A full description of what this configuration is for'),
  ('wylib','data','access','eng','Access','Who is allowed to access this data, and how'),
  ('wylib','data','owner','eng','Owner','The user entity who created and has full permission to the data in this record'),
  ('wylib','data','data','eng','JSON Data','A record in JSON (JavaScript Object Notation) in a format known and controlled by the view or other accessing module'),
  ('wylib','data','crt_date','eng','Created','The date this record was created'),
  ('wylib','data','crt_by','eng','Created By','The user who entered this record'),
  ('wylib','data','mod_date','eng','Modified','The date this record was last modified'),
  ('wylib','data','mod_by','eng','Modified By','The user who last modified this record'),
  ('wylib','data_v','own_name','eng','Owner Name','The name of the person who saved this configuration data'),
  ('wylib','data','ruid','fi','Tunnistaa','Kullekin datatietueelle tuotettu yksilöllinen ID-numero'),
  ('wylib','data','component','fi','Komponentti','GUI:n osa joka käyttää tämä data'),
  ('wylib','data','access','fi','Pääsy','Kuka saa käyttää näitä tietoja ja miten'),
  ('base','addr','addr_ent','eng','Entity ID','The ID number of the entity this address applies to'),
  ('base','addr','addr_seq','eng','Sequence','A unique number assigned to each new address for a given entity'),
  ('base','addr','addr_spec','eng','Address','Street address or PO Box.  This can occupy multiple lines if necessary'),
  ('base','addr','addr_type','eng','Type','The kind of address'),
  ('base','addr','addr_prim','eng','Primary','If checked this is the primary address for contacting this entity'),
  ('base','addr','addr_cmt','eng','Comment','Any other notes about this address'),
  ('base','addr','city','eng','City','The name of the city this address is in'),
  ('base','addr','state','eng','State','The name of the state or province this address is in'),
  ('base','addr','pcode','eng','Zip/Postal','Zip or other mailing code applicable to this address.'),
  ('base','addr','country','eng','Country','The name of the country this address is in.  Use standard international country code abbreviations.'),
  ('base','addr','addr_inact','eng','Inactive','If checked this address is no longer a valid address'),
  ('base','addr','dirty','eng','Dirty','A flag used in the database backend to track whether the primary address needs to be recalculated'),
  ('base','addr','crt_date','eng','Created','The date this record was created'),
  ('base','addr','crt_by','eng','Created By','The user who entered this record'),
  ('base','addr','mod_date','eng','Modified','The date this record was last modified'),
  ('base','addr','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','addr_v','std_name','eng','Entity Name','The name of the entity this address pertains to'),
  ('base','addr_v','addr_prim','eng','Primary','If true this is the primary address for contacting this entity'),
  ('base','addr_prim','prim_ent','eng','Entity','The entity ID number of the main address'),
  ('base','addr_prim','prim_seq','eng','Sequence','The sequence number of the main address'),
  ('base','addr_prim','prim_type','eng','type','The address type this record applies to'),
  ('base','addr_v_flat','bill_addr','eng','Bill Address','First line of the billing address'),
  ('base','addr_v_flat','bill_city','eng','Bill City','Billing address city'),
  ('base','addr_v_flat','bill_state','eng','Bill State','Billing address state'),
  ('base','addr_v_flat','bill_country','eng','Bill Country','Billing address country'),
  ('base','addr_v_flat','bill_pcode','eng','Bill Postal','Billing address postal code'),
  ('base','addr_v_flat','ship_addr','eng','Ship Address','First line of the shipping address'),
  ('base','addr_v_flat','ship_city','eng','Ship City','Shipping address city'),
  ('base','addr_v_flat','ship_state','eng','Ship State','Shipping address state'),
  ('base','addr_v_flat','ship_country','eng','Ship Country','Shipping address country'),
  ('base','addr_v_flat','ship_pcode','eng','Ship Postal','Shipping address postal code'),
  ('base','addr_v_flat','phys_addr','eng','Physical Address','First line of the physical address'),
  ('base','addr_v_flat','phys_city','eng','Physical City','Physical address city'),
  ('base','addr_v_flat','phys_state','eng','Physical State','Physical address state'),
  ('base','addr_v_flat','phys_country','eng','Physical Country','Physical address country'),
  ('base','addr_v_flat','phys_pcode','eng','Physical Postal','Physical address postal code'),
  ('base','addr_v_flat','mail_addr','eng','Mailing Address','First line of the mailing address'),
  ('base','addr_v_flat','mail_city','eng','Mailing City','Mailing address city'),
  ('base','addr_v_flat','mail_state','eng','Mailing State','Mailing address state'),
  ('base','addr_v_flat','mail_country','eng','Mailing Country','Mailing address country'),
  ('base','addr_v_flat','mail_pcode','eng','Mailing Postal','ailing address postal code'),
  ('base','comm','comm_ent','eng','Entity','The ID number of the entity this communication point belongs to'),
  ('base','comm','comm_seq','eng','Sequence','A unique number assigned to each new address for a given entity'),
  ('base','comm','comm_spec','eng','Num/Addr','The number or address to use when communication via this method and communication point'),
  ('base','comm','comm_type','eng','Medium','The method of communication'),
  ('base','comm','comm_prim','eng','Primary','If checked this is the primary method of this type for contacting this entity'),
  ('base','comm','comm_cmt','eng','Comment','Any other notes about this communication point'),
  ('base','comm','comm_inact','eng','Inactive','This box is checked to indicate that this record is no longer current'),
  ('base','comm','crt_date','eng','Created','The date this record was created'),
  ('base','comm','crt_by','eng','Created By','The user who entered this record'),
  ('base','comm','mod_date','eng','Modified','The date this record was last modified'),
  ('base','comm','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','comm_v','std_name','eng','Entity Name','The name of the entity this communication point pertains to'),
  ('base','comm_v','comm_prim','eng','Primary','If true this is the primary method of this type for contacting this entity'),
  ('base','comm_prim','prim_ent','eng','Entity','The entity ID number of the main communication point'),
  ('base','comm_prim','prim_seq','eng','Sequence','The sequence number of the main communication point'),
  ('base','comm_prim','prim_spec','eng','Medium','The communication type this record applies to'),
  ('base','comm_prim','prim_type','eng','type','The communication type this record applies to'),
  ('base','comm_v_flat','web_comm','eng','Web Address','The contact''s web page'),
  ('base','comm_v_flat','cell_comm','eng','Cellular','The contact''s cellular phone number'),
  ('base','comm_v_flat','other_comm','eng','Other','Some other communication point for the contact'),
  ('base','comm_v_flat','pager_comm','eng','Pager','The contact''s pager number'),
  ('base','comm_v_flat','fax_comm','eng','Fax','The contact''s FAX number'),
  ('base','comm_v_flat','email_comm','eng','Email','The contact''s email address'),
  ('base','comm_v_flat','text_comm','eng','Text Message','An email address that will send text to the contact''s phone'),
  ('base','comm_v_flat','phone_comm','eng','Phone','The contact''s telephone number'),
  ('base','country','code','eng','Country Code','The ISO 2-letter country code.  This is the offical value to use when entering countries in wylib applications.'),
  ('base','country','com_name','eng','Country','The common name of the country in English'),
  ('base','country','capital','eng','Capital','The name of the capital city'),
  ('base','country','cur_code','eng','Currency','The standard code for the currency of this country'),
  ('base','country','cur_name','eng','Curr Name','The common name in English of the currency of this country'),
  ('base','country','dial_code','eng','Dial Code','The numeric code to dial when calling this country on the phone'),
  ('base','country','iso_3','eng','Code 3','The ISO 3-letter code for this country (not the wylib standard)'),
  ('base','country','iana','eng','Root Domain','The standard extension for WWW domain names for this country'),
  ('base','ent','id','eng','Entity ID','A unique code assigned to each entity, consisting of the entity type and number'),
  ('base','ent','ent_num','eng','Entity Number','A number assigned to each entity, unique within its own group of entities with the same type'),
  ('base','ent','ent_type','eng','Entity Type','The kind of entity this record represents'),
  ('base','ent','ent_cmt','eng','Ent Comment','Any other notes relating to this entity'),
  ('base','ent','ent_name','eng','Entity Name','Company name, personal surname, or group name'),
  ('base','ent','fir_name','eng','First Name','First given (Robert, Susan, William etc.) for person entities only'),
  ('base','ent','mid_name','eng','Middle Names','One or more middle given or maiden names, for person entities only'),
  ('base','ent','pref_name','eng','Preferred','Preferred first name (Bob, Sue, Bill etc.) for person entities only'),
  ('base','ent','title','eng','Title','A title that prefixes the name (Mr., Chief, Dr. etc.)'),
  ('base','ent','born_date','eng','Born Date','Birth date for person entities or optionally, an incorporation date for entities'),
  ('base','ent','gender','eng','Gender','Whether the person is male (m) or female (f)'),
  ('base','ent','marital','eng','Marital Status','Whether the person is married (m) or single (s)'),
  ('base','ent','username','eng','Username','The login name for this person, if a user on this system'),
  ('base','ent','conn_pub','eng','Connection Key','The public key this user uses to authorize connection to the database'),
  ('base','ent','ent_inact','eng','Inactive','A flag indicating that this entity is no longer current, in business, alive, etc'),
  ('base','ent','country','eng','Country','The country of primary citizenship (for people) or legal organization (companies)'),
  ('base','ent','tax_id','eng','TID/SSN','The number by which the country recognizes this person or company for taxation purposes'),
  ('base','ent','bank','eng','Bank Routing','Bank routing information: bank_number<:.;,>account_number'),
  ('base','ent','proxy','eng','Proxy','ID of another person authorized to act on behalf of this employee where necessary in certain administrative functions of the ERP (like budgetary approvals)'),
  ('base','ent','crt_date','eng','Created','The date this record was created'),
  ('base','ent','crt_by','eng','Created By','The user who entered this record'),
  ('base','ent','mod_date','eng','Modified','The date this record was last modified'),
  ('base','ent','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','ent_v','std_name','eng','Name','The standard format for the entity''s name or, for a person, a standard format: Last, Preferred'),
  ('base','ent_v','frm_name','eng','Formal Name','A person''s full name in a formal format: Last, Title First Middle'),
  ('base','ent_v','cas_name','eng','Casual Name','A person''s full name in a casual format: First Last'),
  ('base','ent_v','giv_name','eng','Given Name','A person''s First given name'),
  ('base','ent_v','age','eng','Age','Age, in years, of the entity'),
  ('base','ent_link','org','eng','Organization ID','The ID of the organization entity that the member entity belongs to'),
  ('base','ent_link','mem','eng','Member ID','The ID of the entity that is a member of the organization'),
  ('base','ent_link','role','eng','Member Role','The function or job description of the member within the organization'),
  ('base','ent_link','supr_path','eng','Super Chain','An ordered list of superiors from the top down for this member in this organization'),
  ('base','ent_link','crt_date','eng','Created','The date this record was created'),
  ('base','ent_link','crt_by','eng','Created By','The user who entered this record'),
  ('base','ent_link','mod_date','eng','Modified','The date this record was last modified'),
  ('base','ent_link','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','ent_link_v','org_name','eng','Org Name','The name of the organization or group entity the member belongs to'),
  ('base','ent_link_v','mem_name','eng','Member Name','The name of the person who belongs to the organization'),
  ('base','ent_link_v','role','eng','Role','The job description or duty of the member with respect to the organization he belongs to'),
  ('base','ent_audit','id','eng','Entity ID','The ID of the entity that was changed'),
  ('base','ent_audit','a_seq','eng','Sequence','A sequential number unique to each alteration'),
  ('base','ent_audit','a_date','eng','Date/Time','Date and time of the change'),
  ('base','ent_audit','a_by','eng','Altered By','The username of the user who made the change'),
  ('base','ent_audit','a_action','eng','Action','The operation that produced the change (update, delete)'),
  ('base','ent_audit','a_column','eng','Column','The name of the column that was changed'),
  ('base','ent_audit','a_value','eng','Value','The old value of the column before the change'),
  ('base','ent_audit','a_reason','eng','Reason','The reason for the change'),
  ('base','language','code','eng','Language Code','The ISO 3-letter language code.  Where a native T-code exists, it is the one used here.'),
  ('base','language','iso_3b','eng','Biblio Code','The ISO bibliographic 3-letter code for this language'),
  ('base','language','iso_2','eng','Code 2','The ISO 2-letter code for this language, if it exists'),
  ('base','language','eng_name','eng','Name in English','The common name of the language English'),
  ('base','language','fra_name','eng','Name in French','The common name of the language in French'),
  ('base','token','token_ent','eng','Token Entity','The id of the user this token is generated for'),
  ('base','token','token_seq','eng','Entity ID','A sequential number assigned to each new token, unique to the user the tokens are for'),
  ('base','token','token','eng','Token','An automatically generated code the user will present to get access'),
  ('base','token','allows','eng','Allowed Access','The type of access this token authorizes.  The value "login" grants the user permission to log in.'),
  ('base','token','used','eng','Used','A time stamp showing when the token was presented back to the system'),
  ('base','token','expires','eng','Expires','A time stamp showing when the token will no longer be valid because it has been too long since it was issued'),
  ('base','token','crt_date','eng','Created','The date this record was created'),
  ('base','token','crt_by','eng','Created By','The user who entered this record'),
  ('base','token','mod_date','eng','Modified','The date this record was last modified'),
  ('base','token','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','token_v','expired','eng','Expired','Indicates that this token is no longer valid because too much time has gone by since it was issued'),
  ('base','token_v','valid','eng','Valid','This token can still be used if it has not yet expired and has never yet been used to connect'),
  ('base','token_v','username','eng','Username','The login name of the user this token belongs to'),
  ('base','token_v','std_name','eng','Name','The standard format for the entity''s name or, for a person, a standard format: Last, Preferred'),
  ('base','parm','module','eng','Module','The system or module within the ERP this setting is applicable to'),
  ('base','parm','parm','eng','Name','The name of the parameter setting'),
  ('base','parm','cmt','eng','Comment','Notes you may want to add about why the setting is set to a particular value'),
  ('base','parm','type','eng','Data Type','Indicates the native data type of this paramter (and hence the particular underlying table it will be stored in.)'),
  ('base','parm','v_int','eng','Integer Value','The parameter value in the case when the type is an integer'),
  ('base','parm','v_date','eng','Date Value','The parameter value in the case when the type is a date'),
  ('base','parm','v_text','eng','Text Value','The parameter value in the case when the type is a character string'),
  ('base','parm','v_float','eng','Float Value','The parameter value in the case when the type is a real number'),
  ('base','parm','v_boolean','eng','Boolean Value','The parameter value in the case when the type is a boolean (true/false) value'),
  ('base','parm','crt_date','eng','Created','The date this record was created'),
  ('base','parm','crt_by','eng','Created By','The user who entered this record'),
  ('base','parm','mod_date','eng','Modified','The date this record was last modified'),
  ('base','parm','mod_by','eng','Modified By','The user who last modified this record'),
  ('base','parm_v','value','eng','Value','The value for the parameter setting, expressed as a string'),
  ('base','parm_audit','module','eng','Module','The module name for the parameter that was changed'),
  ('base','parm_audit','parm','eng','Parameter','The parameter name that was changed'),
  ('base','parm_audit','a_seq','eng','Sequence','A sequential number unique to each alteration'),
  ('base','parm_audit','a_date','eng','Date/Time','Date and time of the change'),
  ('base','parm_audit','a_by','eng','Altered By','The username of the user who made the change'),
  ('base','parm_audit','a_action','eng','Action','The operation that produced the change (update, delete)'),
  ('base','parm_audit','a_column','eng','Column','The name of the column that was changed'),
  ('base','parm_audit','a_value','eng','Value','The old value of the column before the change'),
  ('base','parm_audit','a_reason','eng','Reason','The reason for the change'),
  ('base','priv','grantee','eng','Grantee','The user receiving the privilege'),
  ('base','priv','priv','eng','Privilege','The name of the privilege being granted'),
  ('base','priv','level','eng','Access','What level of access within this privilege (view,use,manage)'),
  ('base','priv','priv_level','eng','Priv Level','Shows the name the privilege level will refer to in the database.  This is formed by joining the privilege name and the level with an underscore.'),
  ('base','priv','cmt','eng','Comment','Comments about this privilege allocation to this user'),
  ('base','priv_v','std_name','eng','Entity Name','The name of the entity being granted the privilege'),
  ('base','priv_v','priv_list','eng','Priv List','In the case where the privilege refers to a group role, this shows which underlying privileges belong to that role.'),
  ('base','priv_v','username','eng','Username','The username within the database for this entity'),
  ('mychips','contracts','domain','eng','Author Domain','The web domain of the contract''s author (such as gnu.org, fsf.org, mychips.org, etc.)'),
  ('mychips','contracts','name','eng','Path Name','A unique name for the contract, which also serves as a URL path, and partial filename such as: mychips/terms/mediation'),
  ('mychips','contracts','version','eng','Version','The version number, starting at 1, of this contract document'),
  ('mychips','contracts','language','eng','Language','The standard 3-letter ISO code for the language in which the covenant is expressed'),
  ('mychips','contracts','title','eng','Title','A brief, descriptive title which will be shown as a document or section header when a contract is rendered'),
  ('mychips','contracts','tag','eng','Section Tag','A short alphanumeric string which can be used as a target for cross references inside the document'),
  ('mychips','contracts','published','eng','Published','The date this version of the covenant was first made available to the public'),
  ('mychips','contracts','sections','eng','Sections','Further sub-sections of contract text, describing the terms and conditions of the contract'),
  ('mychips','contracts','digest','eng','Hash','A SHA-256 hash signature of the document (exclusive of this field) which can be referenced by others to prove the accuracy of the contract'),
  ('mychips','contracts','crt_date','eng','Created','The date this record was created'),
  ('mychips','contracts','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','contracts','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','contracts','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','contracts_v','source','eng','Source URL','The official web address where the author of this document maintains its public access'),
  ('mychips','paths_v','id','eng','Peer ID','Entity ID of the peer this pathway starts with'),
  ('mychips','paths_v','length','eng','Node Length','The number of unique peer nodes in this pathway'),
  ('mychips','paths_v','path','eng','Peer ID List','An array of the entity IDs in this pathway'),
  ('mychips','paths_v','uuids','eng','Tally ID List','An array of the tally IDs in this pathway'),
  ('mychips','paths_v','cycle','eng','Cycled','A flag indicating that the pathway contains a loop'),
  ('mychips','paths_v','circuit','eng','Circuit','A flag indicating that the pathway forms a loop from end to end'),
  ('mychips','paths_v','cost','eng','Cost Ratio','The cost to conduct a lift through this pathway.  A number greater than 1 indicates a lift is not possible.'),
  ('mychips','paths_v','min','eng','Minimum','The smallest number of units desired to be lifted along the pathway'),
  ('mychips','paths_v','max','eng','Maximum','The largest number of units desired to be lifted along the pathway'),
  ('mychips','paths_v','bang','eng','Lift Benefit','The product of the pathway length, and the minimum liftable units.  This gives an idea of the relative benefit of conducting a lift along this pathway.'),
  ('mychips','peers','peer_ent','eng','Entity link','A link to the entities base table'),
  ('mychips','peers','peer_cdi','eng','CHIPs ID','The user''s CHIPs Domain Identifier, or CDI'),
  ('mychips','peers','peer_hid','eng','Covert ID','A substitute ID by which direct trading partners will refer to this user, when conversing with other peers'),
  ('mychips','peers','peer_pub','eng','Peer Public Key','The peer''s public key, known to other trading partners'),
  ('mychips','peers','peer_inet','eng','Peer Net Addr','The IP number where other CHIP servers can connect to do trades with this peer'),
  ('mychips','peers','peer_port','eng','Peer Port','The port where other servers will connect'),
  ('mychips','peers','peer_cmt','eng','Peer Comments','Administrative comments about this peer'),
  ('mychips','peers','crt_date','eng','Created','The date this record was created'),
  ('mychips','peers','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','peers','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','peers','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','peers_v','peer_sock','eng','Peer Socket','The IP Number, and port where other servers can connect to trade with this peer.'),
  ('mychips','tallies','tally_ent','eng','Tally Entity','The ID number of the entity or person this tally belongs to'),
  ('mychips','tallies','tally_seq','eng','Tally Sequence','A unique number among all tallies owned by this entity'),
  ('mychips','tallies','tally_guid','eng','Tally GUID','A globally unique identifier for this tally'),
  ('mychips','tallies','tally_type','eng','Tally Type','Determines if this entity is typically the creditor (stock) or the debtor (foil) for this tally'),
  ('mychips','tallies','tally_date','eng','Tally Date','The date and time this tally was initiated between the parties'),
  ('mychips','tallies','version','eng','Version','A number indicating the format standard this tally adheres to'),
  ('mychips','tallies','partner','eng','Partner Entity','The entity id number of the other party to this tally'),
  ('mychips','tallies','status','eng','Status','Current state of the tally'),
  ('mychips','tallies','request','eng','Request','Requested next state for the tally'),
  ('mychips','tallies','comment','eng','Comment','Any notes the user might want to enter regarding this tally'),
  ('mychips','tallies','user_sig','eng','User Signed','The digital signature of the entity this tally belongs to'),
  ('mychips','tallies','part_sig','eng','Partner Signed','The digital signature of the other party to this tally'),
  ('mychips','tallies','contract','eng','Contract','The hash ID of the standard contract this tally is based upon.'),
  ('mychips','tallies','stock_terms','eng','Stockee Terms','The credit terms by which the holder of the tally stock is governed'),
  ('mychips','tallies','foil_terms','eng','Foilee Terms','The credit terms by which the holder of the tally foil is governed'),
  ('mychips','tallies','bal_target','eng','Target Balance','The ideal total of units the lift administrator should attempt to accumulate when conducting lifts'),
  ('mychips','tallies','lift_marg','eng','Lift Margin','A cost associated with a lift through this tally.  Zero means no cost.  A positive percentage indicates a cost, or disincentive to trade.  For example, 0.01 means a 4% cost for doing a lift.  A negative number means the tally owner will give up some value in order to get lifts done.'),
  ('mychips','tallies','drop_marg','eng','Drop Margin','A cost associated with a reverse lift (or drop) through this tally.  Zero means no cost.  A value of 1 (the default) will effectively prevent reverse lifts.'),
  ('mychips','tallies','cr_lim','eng','Credit Limit','The maximum amount the stock entity will allow the foil entity to accumulate in credit at one time'),
  ('mychips','tallies','dr_lim','eng','Debit Limit','The maximum balance the foil entity will allow the stock to accumulate in the opposite direction of normal credit flow'),
  ('mychips','tallies','units_c','eng','Cached Units','A cached copy of the total of all the chits on this tally, from the perspective of the tally''s owner'),
  ('mychips','tallies_v','state','eng','State','A computed value indicating the state of progress as the tally goes through its lifecycle'),
  ('mychips','tallies_v','action','eng','Action','Indicates this tally requires some kind of action on the part of the user, such as accepting, rejecting, confirming, etc.'),
  ('mychips','chits','chit_ent','eng','Tally Entity','Entity ID of the owner of the tally this chit belongs to'),
  ('mychips','chits','chit_seq','eng','Tally Sequence','Sequence number of the owner of the tally this chit belongs to'),
  ('mychips','chits','chit_idx','eng','Chit Index','A unique identifier within the tally, identifying this chit'),
  ('mychips','chits','chit_guid','eng','Chit GUID','A globally unique identifier for this transaction'),
  ('mychips','chits','chit_type','eng','Chit Type','The type of transaction represented by this flow of credit'),
  ('mychips','chits','chit_date','eng','Date/Time','The date and time when this transaction is effective'),
  ('mychips','chits','amount','eng','Amount','The amount of the transaction, as measured in micro-CHIPs (1/1,000,000)'),
  ('mychips','chits','pro_quo','eng','Quid Pro Quo','A reference to an invoice, a purchase order, a receipt or other document evidencing goods or services rendered, and a trading relationship between the parties'),
  ('mychips','chits','memo','eng','Memo','Any other description or explanation for the transaction'),
  ('mychips','confirms','conf_ent','eng','Confirm Entity','Entity ID of the owner of the tally this confirmation belongs to'),
  ('mychips','confirms','conf_seq','eng','Confirm Sequence','Sequence number of the owner of the tally this confirmation belongs to'),
  ('mychips','confirms','conf_idx','eng','Confirm Index','A unique identifier within the tally, identifying this confirmation'),
  ('mychips','confirms','conf_guid','eng','Confirmation GUID','A globally unique identifier for this confirmation'),
  ('mychips','confirms','conf_date','eng','Date & Time','The date and time when this account total is computed'),
  ('mychips','confirms','sum','eng','Sum','The total of all transaction, or chits, on this tally as of the confirmation moment, and as measured in micro-CHIPs (1/1,000,000)'),
  ('mychips','confirms','signature','eng','Signature','The digital signature of the other party, computed on a record containing the other (non-signature) fields in this table'),
  ('mychips','users','user_ent','eng','Entity link','A link to the entities base table.'),
  ('mychips','users','user_inet','eng','User Net Addr','The IP number where the users''s mobile application connects'),
  ('mychips','users','user_port','eng','User Port','The port to which the user''s mobile device will connect'),
  ('mychips','users','user_stat','eng','Trading Status','The current state of the user''s account for trading of CHIPs'),
  ('mychips','users','user_cmt','eng','User Comments','Administrative comments about this user'),
  ('mychips','users','host_id','eng','Host ID','A unique code identifying the controller server that processes peer traffic for this user'),
  ('mychips','users','crt_date','eng','Created','The date this record was created'),
  ('mychips','users','crt_by','eng','Created By','The user who entered this record'),
  ('mychips','users','mod_date','eng','Modified','The date this record was last modified'),
  ('mychips','users','mod_by','eng','Modified By','The user who last modified this record'),
  ('mychips','users_v','user_sock','eng','User Socket','The IP Number, and port to which the user''s mobile device will connect'),
  ('mychips','users_v','peer_sock','eng','Peer Socket','The IP Number, and port where other servers can connect to trade with this peer.'),
  ('mychips','users','user_ent','fin','Entiteettien linkki','Yhteys yhteisön peruspöytään'),
  ('mychips','users','user_stat','fin','Kaupan tila','CHIP-tilin kaupankäynnin tilille'),
  ('mychips','users_v','mobi_socket','fin','Käyttäjä pistorasia','IP-numero ja portti, johon käyttäjän mobiililaite yhdistää');

insert into wm.value_text (vt_sch,vt_tab,vt_col,value,language,title,help) values
  ('wylib','data','access','priv','eng','Private','Only the owner of this data can read, write or delete it'),
  ('wylib','data','access','read','eng','Public Read','The owner can read and write, all others can read, or see it'),
  ('wylib','data','access','write','eng','Public Write','Anyone can read, write, or delete this data'),
  ('wylib','data','access','priv','fi','Yksityinen','Vain näiden tietojen omistaja voi lukea, kirjoittaa tai poistaa sen'),
  ('wylib','data','access','read','fi','Julkinen Lukea','Omistaja voi lukea ja kirjoittaa, kaikki muut voivat lukea tai nähdä sen'),
  ('wylib','data','access','write','fi','Julkinen Kirjoittaa','Jokainen voi lukea, kirjoittaa tai poistaa näitä tietoja'),
  ('base','addr','addr_type','phys','eng','Physical','Where the entity has people living or working'),
  ('base','addr','addr_type','mail','eng','Mailing','Where mail and correspondence is received'),
  ('base','addr','addr_type','ship','eng','Shipping','Where materials are picked up or delivered'),
  ('base','addr','addr_type','bill','eng','Billing','Where invoices and other accounting information are sent'),
  ('base','comm','comm_type','phone','eng','Phone','A way to contact the entity via telephone'),
  ('base','comm','comm_type','email','eng','Email','A way to contact the entity via email'),
  ('base','comm','comm_type','cell','eng','Cell','A way to contact the entity via cellular telephone'),
  ('base','comm','comm_type','fax','eng','FAX','A way to contact the entity via faxsimile'),
  ('base','comm','comm_type','text','eng','Text Message','A way to contact the entity via email to text messaging'),
  ('base','comm','comm_type','web','eng','Web Address','A World Wide Web address URL for this entity'),
  ('base','comm','comm_type','pager','eng','Pager','A way to contact the entity via a mobile pager'),
  ('base','comm','comm_type','other','eng','Other','Some other contact method for the entity'),
  ('base','ent','ent_type','p','eng','Person','The entity is an individual'),
  ('base','ent','ent_type','o','eng','Organization','The entity is an organization (such as a company or partnership) which may employ or include members of individual people or other organizations'),
  ('base','ent','ent_type','g','eng','Group','The entity is a group of people, companies, and/or other groups'),
  ('base','ent','ent_type','r','eng','Role','The entity is a role or position that may not correspond to a particular person or company'),
  ('base','ent','gender','','eng','N/A','Gender is not applicable (such as for organizations or groups)'),
  ('base','ent','gender','m','eng','Male','The person is male'),
  ('base','ent','gender','f','eng','Female','The person is female'),
  ('base','ent','marital','','eng','N/A','Marital status is not applicable (such as for organizations or groups)'),
  ('base','ent','marital','m','eng','Married','The person is in a current marriage'),
  ('base','ent','marital','s','eng','Single','The person has never married or is divorced or is the survivor of a deceased spouse'),
  ('base','parm','type','int','eng','Integer','The parameter can contain only values of integer type (... -2, -1, 0, 1, 2 ...'),
  ('base','parm','type','date','eng','Date','The parameter can contain only date values'),
  ('base','parm','type','text','eng','Text','The parameter can contain any text value'),
  ('base','parm','type','float','eng','Float','The parameter can contain only values of floating point type (integer portion, decimal, fractional portion)'),
  ('base','parm','type','boolean','eng','Boolean','The parameter can contain only the values of true or false'),
  ('base','priv','level','role','eng','Group Role','The privilege is really a group name which contains other privileges and levels'),
  ('base','priv','level','limit','eng','View Only','Limited access - Can see data but not change it'),
  ('base','priv','level','user','eng','Normal Use','Normal access for the user of this function or module - Includes normal changing of data'),
  ('base','priv','level','super','eng','Supervisor','Supervisory privilege - Typically includes the ability to undo or override normal user functions.  Also includes granting of view, user privileges to others.'),
  ('mychips','tallies','tally_type','stock','eng','Stock','The entity this tally belongs to is typically the creditor on transactions'),
  ('mychips','tallies','tally_type','foil','eng','Foil','The entity this tally belongs to is typically the debtor on transactions'),
  ('mychips','tallies','status','void','eng','Void','The tally has been abandoned before being affirmed by both parties'),
  ('mychips','tallies','status','draft','eng','Draft','The tally have been suggested by one party but not yet accepted by the other party'),
  ('mychips','tallies','status','open','eng','Open','The tally is affirmed by both parties and can be used for trading chits'),
  ('mychips','tallies','status','close','eng','Close','No further trading can occur on this tally'),
  ('mychips','tallies','request','void','eng','Void','One party has requested to abandon the tally agreement'),
  ('mychips','tallies','request','draft','eng','Draft','One party is requesting ???'),
  ('mychips','tallies','request','open','eng','Open','One party is requesting to open a tally according to the specified terms'),
  ('mychips','tallies','request','close','eng','Close','One party is requesting to disable further trading on this tally'),
  ('mychips','chits','chit_type','gift','eng','Gift','The credit is given without any consideration.  Most compliance contracts would deem this unenforceable.'),
  ('mychips','chits','chit_type','lift','eng','Credit Lift','The transaction is part of a credit lift, so multiple chits should exist with the same ID number, which all net to zero in their effect to the relevant entity'),
  ('mychips','chits','chit_type','loan','eng','Loan','The credit is not given, but is advanced with the expectation of a later return.  Consideration would normally be a note of some kind.'),
  ('mychips','chits','chit_type','tran','eng','Transaction','The credit is exchanged for goods or services.  There should be an invoice or receipt referenced evidencing due consideration in order to make this transaction enforceable.'),
  ('mychips','users','user_stat','act','eng','Active','Good to conduct trades'),
  ('mychips','users','user_stat','lck','eng','Lockdown','Account in emergency lockdown.  Do not conduct trades which result in a net loss of credit.'),
  ('mychips','users','user_stat','off','eng','Offline','Account completely off line.  No trades possible.'),
  ('mychips','users','user_stat','act','fin','Aktiivinen','Hyvä käydä kauppaa'),
  ('mychips','users','user_stat','lck','fin','Lukittu','Tili hätätilanteessa. Älä harjoita kauppoja, jotka johtavat nettotappioon.'),
  ('mychips','users','user_stat','off','fin','Irrotettu','Tili kokonaan pois päältä. Kaupat eivät ole mahdollisia.');

insert into wm.message_text (mt_sch,mt_tab,code,language,title,help) values
  ('wylib','data','IAT','eng','Invalid Access Type','Access type must be: priv, read, or write'),
  ('wylib','data','appSave','eng','Save State','Re-save the layout and operating state of the application to the current named configuration, if there is one'),
  ('wylib','data','appSaveAs','eng','Save State As','Save the layout and operating state of the application, and all its subordinate windows, using a named configuration'),
  ('wylib','data','appRestore','eng','Load State','Restore the application layout and operating state from a previously saved state'),
  ('wylib','data','appDefault','eng','Default State','Reload the application to its default state (you will lose any unsaved configuration state)'),
  ('wylib','data','appStatePrompt','eng','Input Tag','A tag to identify this saved state'),
  ('wylib','data','appStateTag','eng','State Tag','The tag is a brief name you will refer to later when loading the saved state'),
  ('wylib','data','appStateDescr','eng','State Description','A full description of the saved state and what you use it for'),
  ('wylib','data','appEditState','eng','Edit States','Preview a list of saved states for this application'),
  ('wylib','data','appServer','eng','Server','Toggle menu for connecting to various servers'),
  ('wylib','data','appServerURL','eng','Server URL','The domain and port of the server you are currently connected to'),
  ('wylib','data','appNoConnect','eng','Not Connected','The application is not connected to a backend server'),
  ('wylib','data','conmenu','eng','Connection Menu','Various helper functions to control how you connect to server sites, and manage your connection keys'),
  ('wylib','data','conTitle','eng','Connection Keys','A list of credentials, servers and ports where you normally connect'),
  ('wylib','data','conConnect','eng','Connect','Attempt to connect to the server at this address and port (or Shift-click to disconnect)'),
  ('wylib','data','conDelete','eng','Delete','Remove the selected server connections from the list'),
  ('wylib','data','conLoad','eng','Load Sites','Get site connection key information previously stored in this browser''s local storage'),
  ('wylib','data','conZap','eng','Forget Sites','Remove site connection key information so it is no longer stored in this browser'),
  ('wylib','data','conLock','eng','Lock Sites','Encrypt this site information in the browser using a code and password so others can not use it'),
  ('wylib','data','conKey','eng','Connect Key','A key that will grant you access to this site.  Do not share this key or store it on a public device or others will be able to access your login.'),
  ('wylib','data','conImport','eng','Import Keys','Drag/drop key files here, or click to import a connection key, or one-time connection ticket'),
  ('wylib','data','conExport','eng','Export Keys','Save the selected private connection keys out to a file.  Delete these files immediately after moving them to a private backup device.  Never leave them in the download area or on a live file system!'),
  ('wylib','data','conRetry','eng','Retrying','Attempting to automatically reconnect to the server'),
  ('wylib','data','conExpFile','eng','Key Filename','The file name to use for saving the selected private keys'),
  ('wylib','data','conUsername','eng','Username','Input the name you will use to connect to the backend database.  If you don''t know.  Ask the person who issued your connection ticket.'),
  ('wylib','data','conNoCrypto','eng','No Crypto Library','Cryptographic functions not found in browser API.  Make sure you are connected by https, or use a more modern browser.'),
  ('wylib','data','conCryptErr','eng','Generating Key','There was an error in the browser attempting to generate a connection key'),
  ('wylib','data','dbe','eng','Edit','Insert, change and delete records from the database view'),
  ('wylib','data','dbeColMenu','eng','Column','Operations you can perform on this column of the preview'),
  ('wylib','data','dbeMenu','eng','Editing','A menu of functions for editing a database record'),
  ('wylib','data','dbeInsert','eng','Add New','Insert a new record into the database table'),
  ('wylib','data','dbeUpdate','eng','Update','Modify changed fields in the existing database record'),
  ('wylib','data','dbeDelete','eng','Delete','Delete this database record (can not be un-done)'),
  ('wylib','data','dbeClear','eng','Clear','Empty the editing fields, discontinue editing any database record that may have been loaded'),
  ('wylib','data','dbeLoadRec','eng','Load Record','Load a specific record from the database by its primary key'),
  ('wylib','data','dbePrimary','eng','Primary Key','The value that uniquely identifies the current record among all the rows in the database table'),
  ('wylib','data','dbeActions','eng','Actions','Perform various commands pertaining to this particular view and record'),
  ('wylib','data','dbePreview','eng','Preview Document','Preview this record as a document'),
  ('wylib','data','dbeSubords','eng','Preview','Toggle the viewing of views and records which relate to the currently loaded record'),
  ('wylib','data','dbeLoadPrompt','eng','Primary Key','Input the primary key values'),
  ('wylib','data','dbeRecordID','eng','Record ID','Load a record by specifying its primary key values directly'),
  ('wylib','data','dbePopupErr','eng','Popup Error','Error trying to open a child window.  Is the browser blocking popup windows?'),
  ('wylib','data','winMenu','eng','Window Functions','A menu of functions for the display and operation of this window'),
  ('wylib','data','winSave','eng','Save State','Re-save the layout and operating state of this window to the current named configuration, if there is one'),
  ('wylib','data','winSaveAs','eng','Save State As','Save the layout and operating state of this window, and all its subordinate windows, to a named configuration'),
  ('wylib','data','winRestore','eng','Load State','Restore the the window''s layout and operating state from a previously saved state'),
  ('wylib','data','winDefault','eng','Default State','Erase locally stored configuration data for this window'),
  ('wylib','data','winModified','eng','Modified Content','Changes may be lost if you close the window'),
  ('wylib','data','winPinned','eng','Window Pinned','Keep this window open until it is explicitly closed'),
  ('wylib','data','winClose','eng','Close Window','Close this window'),
  ('wylib','data','winToTop','eng','Move To Top','Make this window show above others of its peers (can also double click on a window header)'),
  ('wylib','data','winToBottom','eng','Move To Bottom','Place this window behind others of its peers'),
  ('wylib','data','winMinimize','eng','Minimize','Shrink window down to an icon by which it can be re-opened'),
  ('wylib','data','winPopUp','eng','Printable Popup','Make a copy, if possible, of this window in a separate popup window so it can be printed, separate from the rest of the page'),
  ('wylib','data','winPrint','eng','Print Document','Find the nearest independent document (iframe) within this component, and print it'),
  ('wylib','data','winUnknown','eng','Unknown Message','An error or query was generated that could not be understood by the program'),
  ('wylib','data','winUnCode','eng','Unknown Error Code','An error message was returned with an unrecognized code or status'),
  ('wylib','data','dbp','eng','Preview','A window for showing the records of a database table in a grid like a spreadsheet'),
  ('wylib','data','dbpMenu','eng','Preview Menu','A menu of functions for operating on the preview list below'),
  ('wylib','data','dbpReload','eng','Reload','Reload the records specified in the previous load'),
  ('wylib','data','dbpLoad','eng','Load Default','Load the records shown in this view, by default'),
  ('wylib','data','dbpLoadAll','eng','Load All','Load all records from this table'),
  ('wylib','data','dbpDefault','eng','Default Columns','Set all column display and order to the database default'),
  ('wylib','data','dbpFilter','eng','Filter','Load records according to filter criteria'),
  ('wylib','data','dbpAutoLoad','eng','Auto Execute','Automatically execute the top row any time the preview is reloaded'),
  ('wylib','data','dbpColumn','eng','Column Menu','Menu of commands to control this column display'),
  ('wylib','data','dbpVisible','eng','Visible','Specify which columns are visible in the preview'),
  ('wylib','data','dbpVisCheck','eng','Visible','Check the box to make this column visible'),
  ('wylib','data','dbpColAuto','eng','Auto Size','Adjust the width of this column to be optimal for its contents'),
  ('wylib','data','dbpColHide','eng','Hide Column','Remove this column from the display'),
  ('wylib','data','dbpNext','eng','Next Record','Move the selection down one line and execute (normally edit) that new line'),
  ('wylib','data','dbpPrev','eng','Prior Record','Move the selection up one line and execute (normally edit) that new line'),
  ('wylib','data','X.dbpColSel','eng','Visible Columns','Show or hide individual columns'),
  ('wylib','data','X.dbpFooter','eng','Footer','Check the box to turn on column summaries, at the bottom'),
  ('wylib','data','dbs','eng','Filter Search','Load records according to filter criteria'),
  ('wylib','data','dbsSearch','eng','Query Search','Run the configured selection query, returning matching records'),
  ('wylib','data','dbsSave','eng','Save Query','Save the current query for future use'),
  ('wylib','data','dbsRecall','eng','Recall Query','Recall a named query which has been previously saved'),
  ('wylib','data','dbsEqual','eng','=','The left and right side of the comparison are equal'),
  ('wylib','data','dbsLess','eng','<','The left value is less than the value on the right'),
  ('wylib','data','dbsLessEq','eng','<=','The left value is less than or equal to the value on the right'),
  ('wylib','data','dbsMore','eng','>','The left value is greater than the value on the right'),
  ('wylib','data','dbsMoreEq','eng','>=','The left value is greater than or equal to the value on the right'),
  ('wylib','data','dbsRexExp','eng','~','The left value matches a regular expression given on the value on the right'),
  ('wylib','data','dbsDiff','eng','Diff','The left side is different from the right, in a comparison where two nulls (unassigned values) can be thought of as being the same'),
  ('wylib','data','dbsIn','eng','In','The left value exists in a comma separated list you specify, or an array in another database field'),
  ('wylib','data','dbsNull','eng','Null','The value on the left is a null, or not assigned'),
  ('wylib','data','dbsTrue','eng','True','The left value is a boolean with a true value'),
  ('wylib','data','dbsNop','eng','<Nop>','This operation causes the whole comparison clause to be ignored'),
  ('wylib','data','diaDialog','eng','Dialog','Query user for specified input values or parameters'),
  ('wylib','data','diaReport','eng','Report','Report window'),
  ('wylib','data','diaOK','eng','OK','Acknowledge you have seen the posted message'),
  ('wylib','data','diaYes','eng','OK','Proceed with the proposed operation and close the dialog'),
  ('wylib','data','diaCancel','eng','Cancel','Abandon the operation associated with the dialog'),
  ('wylib','data','diaApply','eng','Perform','Perform the action associated with this dialog, but do not close it'),
  ('wylib','data','diaError','eng','Error','Something went wrong'),
  ('wylib','data','diaNotice','eng','Notice','The message is a warning or advice for the user'),
  ('wylib','data','diaConfirm','eng','Confirm','The user is asked to confirm before proceeding, or cancel to abandon the operation'),
  ('wylib','data','diaQuery','eng','Input','The user is asked for certain input data, and a confirmation before proceeding'),
  ('wylib','data','mdewMore','eng','More Fields','Click to see more data fields pertaining to this record'),
  ('wylib','data','23505','eng','Key Violation','An operation would have resulted in multiple records having duplicated data, which is required to be unique'),
  ('wylib','data','subWindow','eng','Subordinate View','Open a preview of records in another table that relate to the currently loaded record from this view'),
  ('wylib','data','litToSub','eng','To Subgroup','Move this item to a deeper sub-group'),
  ('wylib','data','litLeft','eng','Left Side','Specify a field from the database to compare'),
  ('wylib','data','litRight','eng','Right Side','Specify a field from the database, or manual entry to compare'),
  ('wylib','data','litManual','eng','Manual Entry','Enter a value manually to the right'),
  ('wylib','data','litRightVal','eng','Right Value','Specify an explicit right-hand value for the comparision'),
  ('wylib','data','litRemove','eng','Remove Item','Remove this item from the comparison list'),
  ('wylib','data','litNot','eng','Not','If asserted, the sense of the comparison will be negated, or made opposite'),
  ('wylib','data','litCompare','eng','Comparison','Specify an operator for the comparison'),
  ('wylib','data','lstAndOr','eng','And/Or','Specify whether all conditions must be true (and), or just one or more (or)'),
  ('wylib','data','lstAddCond','eng','Add Condition','Add another condition for comparison'),
  ('wylib','data','lstRemove','eng','Remove Grouping','Remove this group of conditions'),
  ('wylib','data','sdc','eng','Structured Document','An editor for documents structured in an outline format'),
  ('wylib','data','sdcMenu','eng','Document Menu','A menu of functions for working with structured documents'),
  ('wylib','data','sdcUpdate','eng','Update','Save changes to this document back to the database'),
  ('wylib','data','sdcUndo','eng','Undo','Reverse the effect of a paragraph deletion or move'),
  ('wylib','data','sdcClear','eng','Clear','Delete the contents of the document on the screen.  Does not affect the database.'),
  ('wylib','data','sdcClearAsk','eng','Clear WorkSpace','Are you sure you want to clear the document data?'),
  ('wylib','data','sdcImport','eng','File Import','Load the workspace from an externally saved file'),
  ('wylib','data','sdcImportAsk','eng','Import File','Select a file to Import, or drag it onto the import button'),
  ('wylib','data','sdcExport','eng','File Export','Save the workspace to an external file'),
  ('wylib','data','sdcExportAsk','eng','Export File','Input a filename to use when exporting'),
  ('wylib','data','sdcExportFmt','eng','Human Readable','Export the file with indentation to make it more easily readable by people'),
  ('wylib','data','sdcSpell','eng','Spell Checking','Enable/disable spell checking in on the screen'),
  ('wylib','data','sdcBold','eng','Bold','Mark the highlighted text as bold'),
  ('wylib','data','sdcItalic','eng','Italic','Mark the highlighted text as italic'),
  ('wylib','data','sdcUnder','eng','Underline','Underline highlighted text'),
  ('wylib','data','sdcCross','eng','Cross Reference','Wrap the highlighted text with a cross reference.  The text should be a tag name for another section.  That section number will be substituted for the tag name.'),
  ('wylib','data','sdcTitle','eng','Title','An optional title for this section or paragraph'),
  ('wylib','data','sdcSection','eng','Section','Click to edit text.  Double click at edge for direct editing mode.  Drag at edge to move.'),
  ('wylib','data','sdcTag','eng','Tag','An identifying word that can be used to cross-reference to this section or paragraph'),
  ('wylib','data','sdcText','eng','Paragraph Text','Insert/Edit the raw paragraph text directly here, including entering limited HTML tags, if desired'),
  ('wylib','data','sdcEdit','eng','Direct Editing','This section or paragraph is in direct editing mode.  Double click on the background to return to preview mode.'),
  ('wylib','data','sdcAdd','eng','Add Subsection','Create a new paragraph or section nested below this one'),
  ('wylib','data','sdcDelete','eng','Delete Section','Delete this paragraph or section of the document'),
  ('wylib','data','sdcEditAll','eng','Edit All','Put all paragraphs or sections into direct editing mode.  This can be done one at a time by double clicking on the paragraph.'),
  ('wylib','data','sdcPrevAll','eng','Preview All','Take all paragraphs or sections out of direct editing mode, and into preview mode'),
  ('wylib','data','X','eng',null,null),
  ('wylib','data','IAT','fi','Virheellinen käyttötyyppi','Käytön tyypin on oltava: priv, lukea tai kirjoittaa'),
  ('wylib','data','dbpMenu','fi','Esikatselu','Toimintojen valikko, joka toimii alla olevassa esikatselussa'),
  ('wylib','data','dbpReload','fi','Ladata','Päivitä edellisessä kuormassa määritetyt tietueet'),
  ('wylib','data','dbpLoad','fi','Ladata Oletus','Aseta tässä näkymässä näkyvät kirjaukset oletuksena'),
  ('wylib','data','dbpLoadAll','fi','Loadata Kaikki','Lataa kaikki taulukon tiedot'),
  ('wylib','data','dbpFilter','fi','Suodattaa','Lataa tietueet suodatuskriteerien mukaisesti'),
  ('wylib','data','dbpVisible','fi','Näkyvyys','Sarakkeiden valikko, josta voit päättää, mitkä näkyvät esikatselussa'),
  ('wylib','data','dbpVisCheck','fi','Ilmoita näkyvyydestä','Kirjoita tämä ruutu näkyviin, jotta tämä sarake voidaan näyttää'),
  ('wylib','data','dbpFooter','fi','Yhteenveto','Ota ruutuun käyttöön sarakeyhteenveto'),
  ('wylib','data','dbeActions','fi','Tehköjä','Tehdä muutamia asioita tämän mukaisesti'),
  ('base','addr','CCO','eng','Country','The country must always be specified (and in standard form)'),
  ('base','addr','CPA','eng','Primary','There must be at least one address checked as primary'),
  ('base','comm','CPC','eng','Primary','There must be at least one communication point of each type checked as primary'),
  ('base','ent','CFN','eng','First Name','A first name is required for personal entities'),
  ('base','ent','CMN','eng','Middle Name','A middle name is prohibited for non-personal entities'),
  ('base','ent','CPN','eng','Pref Name','A preferred name is prohibited for non-personal entities'),
  ('base','ent','CTI','eng','Title','A preferred title is prohibited for non-personal entities'),
  ('base','ent','CGN','eng','Gender','Gender must not be specified for non-personal entities'),
  ('base','ent','CMS','eng','Marital','Marital status must not be specified for non-personal entities'),
  ('base','ent','CBD','eng','Born Date','A born date is required for inside people'),
  ('base','ent','CPA','eng','Prime Addr','A primary address must be active'),
  ('base','ent_v','directory','eng','Directory','Report showing basic contact data for the selected entities'),
  ('base','ent_link','NBP','eng','Illegal Entity Org','A personal entity can not be an organization (and have member entities)'),
  ('base','ent_link','PBC','eng','Illegal Entity Member','Only personal entities can belong to company entities'),
  ('base','priv','NUN','eng','No username found','The specified user has no username--This probably means he has not been added as a database user'),
  ('base','priv','UAE','eng','User already exists','The specified username was found to already exist as a user in the database'),
  ('base','priv','ENF','eng','Employee not found','While adding a user, the specified ID was not found to belong to anyone in the empl database table'),
  ('base','priv','UAD','eng','User doesn''t exist','While dropping a user, the specified username was not found to exist in the database'),
  ('base','priv','UNF','eng','Username not found','While dropping a user, the specified username was not found to exist in the empl database'),
  ('base','priv_v','adduser','eng','Add as User','Create a user account for the selected entity'),
  ('mychips','contracts','BVN','eng','Bad Version Number','Version number for contracts should start with 1 and move progressively larger'),
  ('mychips','contracts','PBC','eng','Publish Constraints','When publishing a document, one must specify the digest hash, the source location, and the content sections'),
  ('mychips','contracts','UNC','eng','Unknown Command','The contract editor report received an unrecognized action command'),
  ('mychips','contracts_v','edit','eng','Edit Sections','Dedicated window for properly editing the contract sections'),
  ('mychips','contracts_v','publish','eng','Publish','Commit this version, write the publication date, and disable further modifications'),
  ('mychips','contracts_v','IDK','eng','Invalid Key','The key values specified for the contract document are not valid'),
  ('mychips','contracts_v','TMK','eng','Wrong Keys','The report is designed to handle exactly one record key'),
  ('mychips','tallies','LMG','eng','Invalid Lift Margin','The lift margin should be specified as a number between -1 and 1, non-inclusive.  More normally, it should be a fractional number such as 0.05, which would assert a 5% cost on lifts, or -0.02 which would give a 2% bonus for doing a lift.'),
  ('mychips','tallies','DMG','eng','Invalid Drop Margin','The drop margin should be specified as a number between 0 and 1, inclusive.  More normally, it should be a fractional number such as 0.2, which would assert a 20% cost on reverse lifts.'),
  ('mychips','users','ABC','eng','Test 1','A test message 1'),
  ('mychips','users','BCD','eng','Test 2','A test message 2'),
  ('mychips','users','DEF','eng','Test 3','A test message 3'),
  ('mychips','users_v','ticket','eng','User Ticket','Generate a temporary, one-time pass to allow a user to establish a secure connection with the server'),
  ('mychips','users_v','lock','eng','Lock Account','Put the specified account(s) into lockdown mode, so no further trading can occur'),
  ('mychips','users_v','unlock','eng','Unlock Account','Put the specified account(s) into functional mode, so normal trading can occur'),
  ('mychips','users_v','summary','eng','Summary Report','Report about the current status of the selected user'),
  ('mychips','users_v','trade','eng','Trading Report','Report showing trades in a given date range'),
  ('mychips','users_v','trade.start','eng','Start Date','Include trades on and after this date'),
  ('mychips','users_v','trade.end','eng','End Date','Include trades on and before this date'),
  ('mychips','users','ABC','fin','Koetus 1','Ensimmäinen testiviesti'),
  ('mychips','users','BCD','fin','Koetus 2','Toinen testiviesti'),
  ('mychips','users','DEF','fin','Koetus 3','Kolmanen testiviesti');

insert into wm.table_style (ts_sch,ts_tab,sw_name,sw_value,inherit) values
  ('wm','table_text','focus','"code"','t'),
  ('wm','column_text','focus','"code"','t'),
  ('wm','value_text','focus','"code"','t'),
  ('wm','message_text','focus','"code"','t'),
  ('wm','column_pub','focus','"code"','t'),
  ('wm','objects','focus','"obj_nam"','t'),
  ('base','addr','focus','"addr_spec"','t'),
  ('base','addr_v','display','["addr_type","addr_spec","state","city","pcode","country","addr_cmt","addr_seq"]','t'),
  ('base','comm','focus','"comm_spec"','t'),
  ('base','comm_v','display','["comm_type","comm_spec","comm_cmt","comm_seq"]','t'),
  ('base','ent','display','["id","ent_type","ent_name","fir_name","born_date"]','t'),
  ('base','ent','focus','"ent_name"','t'),
  ('base','ent_v','actions','[{"name":"directory"}]','f'),
  ('base','ent_v','subviews','["base.addr_v","base.comm_v","base.priv_v"]','t'),
  ('base','ent_v_pub','focus','"ent_name"','t'),
  ('base','ent_link','focus','"org_id"','t'),
  ('base','parm_v','display','["module","parm","type","value","cmt"]','t'),
  ('base','parm_v','focus','"module"','t'),
  ('base','priv','focus','"priv"','t'),
  ('base','priv_v','actions','[{"name":"adduser"}]','f'),
  ('mychips','contracts','display','["domain","name","version","language","released","source","title"]','t'),
  ('mychips','contracts','focus','"domain"','t'),
  ('mychips','contracts_v','actions','[{"name":"edit","format":"strdoc"},{"name":"publish","ask":"1"}]','f'),
  ('mychips','paths_v','display','["id","length","cost","min","circuit","path","circuit"]','t'),
  ('mychips','peers','focus','"ent_name"','t'),
  ('mychips','peers_v','display','["id","std_name","peer_cdi","peer_sock","ent_type","born_date","!fir_name","!ent_name"]','t'),
  ('mychips','peers_v_flat','display','["id","peer_cdi","std_name","bill_addr","bill_city","bill_state"]','t'),
  ('mychips','users','focus','"ent_name"','t'),
  ('mychips','users_v','actions','[{"name":"ticket","format":"html","single":"1"},{"name":"lock","ask":"1"},{"name":"unlock","ask":"1"},{"name":"summary"},{"name":"trade","options":[{"tag":"start","type":"date","style":"ent","size":"11","subframe":"1 1","special":"cal","hint":"date","template":"date"},{"tag":"end","type":"date","style":"ent","size":"11","subframe":"1 2","special":"cal","hint":"date","template":"date"}],"format":"html"}]','f'),
  ('mychips','users_v','display','["id","std_name","ent_type","user_stat","user_sock","born_date","!fir_name","!ent_name"]','t'),
  ('mychips','users_v','subviews','["base.addr_v","base.comm_v"]','t'),
  ('mychips','users_v_flat','display','["id","user_cdi","std_name","bill_addr","bill_city","bill_state"]','t');

insert into wm.column_style (cs_sch,cs_tab,cs_col,sw_name,sw_value) values
  ('wm','table_text','language','size','4'),
  ('wm','table_text','title','size','40'),
  ('wm','table_text','help','size','40'),
  ('wm','table_text','help','special','edw'),
  ('wm','table_text','code','focus','true'),
  ('wm','column_text','language','size','4'),
  ('wm','column_text','title','size','40'),
  ('wm','column_text','help','size','40'),
  ('wm','column_text','help','special','edw'),
  ('wm','column_text','code','focus','true'),
  ('wm','value_text','language','size','4'),
  ('wm','value_text','title','size','40'),
  ('wm','value_text','help','size','40'),
  ('wm','value_text','help','special','edw'),
  ('wm','value_text','code','focus','true'),
  ('wm','message_text','language','size','4'),
  ('wm','message_text','title','size','40'),
  ('wm','message_text','help','size','40'),
  ('wm','message_text','help','special','edw'),
  ('wm','message_text','code','focus','true'),
  ('wm','column_pub','language','size','4'),
  ('wm','column_pub','title','size','40'),
  ('wm','column_pub','help','size','40'),
  ('wm','column_pub','help','special','edw'),
  ('wm','column_pub','code','focus','true'),
  ('wm','objects','name','size','40'),
  ('wm','objects','checked','size','4'),
  ('wm','objects','clean','size','4'),
  ('wm','objects','mod_ver','size','4'),
  ('wm','objects','deps','size','40'),
  ('wm','objects','deps','special','edw'),
  ('wm','objects','ndeps','size','40'),
  ('wm','objects','ndeps','special','edw'),
  ('wm','objects','grants','size','40'),
  ('wm','objects','grants','special','edw'),
  ('wm','objects','col_data','size','40'),
  ('wm','objects','col_data','special','edw'),
  ('wm','objects','crt_sql','size','40'),
  ('wm','objects','crt_sql','special','edw'),
  ('wm','objects','drp_sql','size','40'),
  ('wm','objects','drp_sql','special','edw'),
  ('wm','objects','min_rel','size','4'),
  ('wm','objects','max_rel','size','4'),
  ('wm','objects','obj_nam','focus','true'),
  ('base','addr','addr_seq','style','ent'),
  ('base','addr','addr_seq','size','4'),
  ('base','addr','addr_seq','subframe','10 1'),
  ('base','addr','addr_seq','state','readonly'),
  ('base','addr','addr_seq','justify','r'),
  ('base','addr','addr_seq','hide','1'),
  ('base','addr','addr_seq','write','0'),
  ('base','addr','pcode','style','ent'),
  ('base','addr','pcode','size','10'),
  ('base','addr','pcode','subframe','1 1'),
  ('base','addr','pcode','special','zip'),
  ('base','addr','city','style','ent'),
  ('base','addr','city','size','24'),
  ('base','addr','city','subframe','2 1'),
  ('base','addr','state','style','ent'),
  ('base','addr','state','size','4'),
  ('base','addr','state','subframe','3 1'),
  ('base','addr','state','special','scm'),
  ('base','addr','state','data','state'),
  ('base','addr','addr_spec','style','ent'),
  ('base','addr','addr_spec','size','30'),
  ('base','addr','addr_spec','subframe','1 2 2'),
  ('base','addr','addr_spec','special','edw'),
  ('base','addr','country','style','ent'),
  ('base','addr','country','size','4'),
  ('base','addr','country','subframe','3 2'),
  ('base','addr','country','special','scm'),
  ('base','addr','country','data','country'),
  ('base','addr','addr_type','style','pdm'),
  ('base','addr','addr_type','size','6'),
  ('base','addr','addr_type','subframe','1 3'),
  ('base','addr','addr_type','initial','mail'),
  ('base','addr','addr_inact','style','chk'),
  ('base','addr','addr_inact','size','2'),
  ('base','addr','addr_inact','subframe','2 3'),
  ('base','addr','addr_inact','initial','false'),
  ('base','addr','physical','style','chk'),
  ('base','addr','physical','size','2'),
  ('base','addr','physical','subframe','3 3'),
  ('base','addr','physical','initial','true'),
  ('base','addr','addr_cmt','style','ent'),
  ('base','addr','addr_cmt','size','50'),
  ('base','addr','addr_cmt','subframe','1 5 4'),
  ('base','addr','addr_cmt','special','edw'),
  ('base','addr','addr_ent','style','ent'),
  ('base','addr','addr_ent','size','5'),
  ('base','addr','addr_ent','subframe','1 6'),
  ('base','addr','addr_ent','optional','1'),
  ('base','addr','addr_ent','state','readonly'),
  ('base','addr','addr_ent','justify','r'),
  ('base','addr','dirty','style','chk'),
  ('base','addr','dirty','size','2'),
  ('base','addr','dirty','subframe',''),
  ('base','addr','dirty','hide','1'),
  ('base','addr','dirty','write','0'),
  ('base','addr','crt_by','style','ent'),
  ('base','addr','crt_by','size','10'),
  ('base','addr','crt_by','subframe','1 98'),
  ('base','addr','crt_by','optional','1'),
  ('base','addr','crt_by','write','0'),
  ('base','addr','crt_by','state','readonly'),
  ('base','addr','crt_date','style','inf'),
  ('base','addr','crt_date','size','18'),
  ('base','addr','crt_date','subframe','2 98'),
  ('base','addr','crt_date','optional','1'),
  ('base','addr','crt_date','write','0'),
  ('base','addr','crt_date','state','readonly'),
  ('base','addr','mod_by','style','ent'),
  ('base','addr','mod_by','size','10'),
  ('base','addr','mod_by','subframe','1 99'),
  ('base','addr','mod_by','optional','1'),
  ('base','addr','mod_by','write','0'),
  ('base','addr','mod_by','state','readonly'),
  ('base','addr','mod_date','style','inf'),
  ('base','addr','mod_date','size','18'),
  ('base','addr','mod_date','subframe','2 99'),
  ('base','addr','mod_date','optional','1'),
  ('base','addr','mod_date','write','0'),
  ('base','addr','mod_date','state','readonly'),
  ('base','addr','pcode','focus','true'),
  ('base','addr_v','std_name','style','ent'),
  ('base','addr_v','std_name','size','14'),
  ('base','addr_v','std_name','subframe','2 6 2'),
  ('base','addr_v','std_name','optional','1'),
  ('base','addr_v','std_name','depend','addr_ent'),
  ('base','addr_v','std_name','title',':'),
  ('base','addr_v','std_name','inside','addr_ent'),
  ('base','addr_v','addr_prim','style','chk'),
  ('base','addr_v','addr_prim','size','2'),
  ('base','addr_v','addr_prim','subframe','3 3'),
  ('base','addr_v','addr_prim','initial','false'),
  ('base','addr_v','addr_seq','display','8'),
  ('base','addr_v','addr_spec','display','2'),
  ('base','addr_v','city','display','4'),
  ('base','addr_v','state','display','3'),
  ('base','addr_v','pcode','display','5'),
  ('base','addr_v','country','display','6'),
  ('base','addr_v','addr_cmt','display','7'),
  ('base','addr_v','addr_type','display','1'),
  ('base','addr_v','addr_seq','sort','2'),
  ('base','addr_v','addr_type','sort','1'),
  ('base','comm','comm_seq','style','ent'),
  ('base','comm','comm_seq','size','5'),
  ('base','comm','comm_seq','subframe','0 1'),
  ('base','comm','comm_seq','state','readonly'),
  ('base','comm','comm_seq','justify','r'),
  ('base','comm','comm_seq','hide','1'),
  ('base','comm','comm_seq','write','0'),
  ('base','comm','comm_spec','style','ent'),
  ('base','comm','comm_spec','size','28'),
  ('base','comm','comm_spec','subframe','1 1 3'),
  ('base','comm','comm_type','style','pdm'),
  ('base','comm','comm_type','size','5'),
  ('base','comm','comm_type','subframe','1 2'),
  ('base','comm','comm_type','initial','phone'),
  ('base','comm','comm_inact','style','chk'),
  ('base','comm','comm_inact','size','2'),
  ('base','comm','comm_inact','subframe','2 2'),
  ('base','comm','comm_inact','initial','false'),
  ('base','comm','comm_inact','onvalue','true'),
  ('base','comm','comm_inact','offvalue','false'),
  ('base','comm','comm_cmt','style','ent'),
  ('base','comm','comm_cmt','size','50'),
  ('base','comm','comm_cmt','subframe','1 3 3'),
  ('base','comm','comm_cmt','special','edw'),
  ('base','comm','comm_ent','style','ent'),
  ('base','comm','comm_ent','size','5'),
  ('base','comm','comm_ent','subframe','1 5'),
  ('base','comm','comm_ent','optional','1'),
  ('base','comm','comm_ent','state','readonly'),
  ('base','comm','comm_ent','justify','r'),
  ('base','comm','crt_by','style','ent'),
  ('base','comm','crt_by','size','10'),
  ('base','comm','crt_by','subframe','1 98'),
  ('base','comm','crt_by','optional','1'),
  ('base','comm','crt_by','write','0'),
  ('base','comm','crt_by','state','readonly'),
  ('base','comm','crt_date','style','inf'),
  ('base','comm','crt_date','size','18'),
  ('base','comm','crt_date','subframe','2 98'),
  ('base','comm','crt_date','optional','1'),
  ('base','comm','crt_date','write','0'),
  ('base','comm','crt_date','state','readonly'),
  ('base','comm','mod_by','style','ent'),
  ('base','comm','mod_by','size','10'),
  ('base','comm','mod_by','subframe','1 99'),
  ('base','comm','mod_by','optional','1'),
  ('base','comm','mod_by','write','0'),
  ('base','comm','mod_by','state','readonly'),
  ('base','comm','mod_date','style','inf'),
  ('base','comm','mod_date','size','18'),
  ('base','comm','mod_date','subframe','2 99'),
  ('base','comm','mod_date','optional','1'),
  ('base','comm','mod_date','write','0'),
  ('base','comm','mod_date','state','readonly'),
  ('base','comm','comm_spec','focus','true'),
  ('base','comm_v','std_name','style','ent'),
  ('base','comm_v','std_name','size','14'),
  ('base','comm_v','std_name','subframe','2 5 2'),
  ('base','comm_v','std_name','optional','1'),
  ('base','comm_v','std_name','depend','comm_ent'),
  ('base','comm_v','std_name','title',':'),
  ('base','comm_v','std_name','inside','comm_ent'),
  ('base','comm_v','comm_prim','style','chk'),
  ('base','comm_v','comm_prim','size','2'),
  ('base','comm_v','comm_prim','subframe','3 2'),
  ('base','comm_v','comm_prim','initial','false'),
  ('base','comm_v','comm_prim','onvalue','t'),
  ('base','comm_v','comm_prim','offvalue','f'),
  ('base','comm_v','comm_seq','display','4'),
  ('base','comm_v','comm_type','display','1'),
  ('base','comm_v','comm_spec','display','2'),
  ('base','comm_v','comm_cmt','display','3'),
  ('base','comm_v','comm_seq','sort','2'),
  ('base','comm_v','comm_type','sort','1'),
  ('base','ent','id','style','ent'),
  ('base','ent','id','size','7'),
  ('base','ent','id','subframe','0 1'),
  ('base','ent','id','hide','1'),
  ('base','ent','id','write','0'),
  ('base','ent','id','justify','r'),
  ('base','ent','ent_type','style','pdm'),
  ('base','ent','ent_type','size','2'),
  ('base','ent','ent_type','subframe','3 1'),
  ('base','ent','ent_type','initial','p'),
  ('base','ent','title','style','ent'),
  ('base','ent','title','size','8'),
  ('base','ent','title','subframe','1 2'),
  ('base','ent','title','special','exs'),
  ('base','ent','title','template','^[a-zA-Z\.]*$'),
  ('base','ent','ent_name','style','ent'),
  ('base','ent','ent_name','size','40'),
  ('base','ent','ent_name','subframe','1 1 2'),
  ('base','ent','ent_name','template','^[\w\. ]+$'),
  ('base','ent','fir_name','style','ent'),
  ('base','ent','fir_name','size','14'),
  ('base','ent','fir_name','subframe','2 2'),
  ('base','ent','fir_name','background','#e0f0ff'),
  ('base','ent','fir_name','template','alpha'),
  ('base','ent','mid_name','style','ent'),
  ('base','ent','mid_name','size','12'),
  ('base','ent','mid_name','subframe','3 2'),
  ('base','ent','mid_name','template','alpha'),
  ('base','ent','pref_name','style','ent'),
  ('base','ent','pref_name','size','12'),
  ('base','ent','pref_name','subframe','1 3'),
  ('base','ent','pref_name','template','alpha'),
  ('base','ent','ent_inact','style','chk'),
  ('base','ent','ent_inact','size','2'),
  ('base','ent','ent_inact','subframe','3 3'),
  ('base','ent','ent_inact','initial','f'),
  ('base','ent','ent_inact','onvalue','t'),
  ('base','ent','ent_inact','offvalue','f'),
  ('base','ent','born_date','style','ent'),
  ('base','ent','born_date','size','11'),
  ('base','ent','born_date','subframe','1 4'),
  ('base','ent','born_date','special','cal'),
  ('base','ent','born_date','hint','date'),
  ('base','ent','born_date','template','date'),
  ('base','ent','gender','style','pdm'),
  ('base','ent','gender','size','2'),
  ('base','ent','gender','subframe','2 4'),
  ('base','ent','gender','initial',''),
  ('base','ent','marital','style','pdm'),
  ('base','ent','marital','size','2'),
  ('base','ent','marital','subframe','3 4'),
  ('base','ent','marital','initial',''),
  ('base','ent','bank','style','ent'),
  ('base','ent','bank','size','14'),
  ('base','ent','bank','subframe','1 5'),
  ('base','ent','bank','template','^(|\d+:\d+|\d+:\d+:\d+)$'),
  ('base','ent','bank','hint','####:#### or ####:####:s'),
  ('base','ent','username','style','ent'),
  ('base','ent','username','size','12'),
  ('base','ent','username','subframe','2 5'),
  ('base','ent','username','template','alnum'),
  ('base','ent','conn_key','style','ent'),
  ('base','ent','conn_key','size','8'),
  ('base','ent','conn_key','subframe','3 5'),
  ('base','ent','conn_key','write','0'),
  ('base','ent','tax_id','style','ent'),
  ('base','ent','tax_id','size','10'),
  ('base','ent','tax_id','subframe','1 6'),
  ('base','ent','tax_id','hint','###-##-####'),
  ('base','ent','country','style','ent'),
  ('base','ent','country','size','4'),
  ('base','ent','country','subframe','2 6'),
  ('base','ent','country','special','scm'),
  ('base','ent','country','data','country'),
  ('base','ent','proxy','style','ent'),
  ('base','ent','proxy','size','6'),
  ('base','ent','proxy','subframe','3 6'),
  ('base','ent','proxy','special','scm'),
  ('base','ent','proxy','data','ent'),
  ('base','ent','ent_cmt','style','mle'),
  ('base','ent','ent_cmt','size','80'),
  ('base','ent','ent_cmt','subframe','1 7 3'),
  ('base','ent','ent_cmt','special','edw'),
  ('base','ent','crt_by','style','ent'),
  ('base','ent','crt_by','size','10'),
  ('base','ent','crt_by','subframe','1 98'),
  ('base','ent','crt_by','optional','1'),
  ('base','ent','crt_by','write','0'),
  ('base','ent','crt_by','state','readonly'),
  ('base','ent','crt_date','style','inf'),
  ('base','ent','crt_date','size','18'),
  ('base','ent','crt_date','subframe','2 98'),
  ('base','ent','crt_date','optional','1'),
  ('base','ent','crt_date','write','0'),
  ('base','ent','crt_date','state','readonly'),
  ('base','ent','mod_by','style','ent'),
  ('base','ent','mod_by','size','10'),
  ('base','ent','mod_by','subframe','1 99'),
  ('base','ent','mod_by','optional','1'),
  ('base','ent','mod_by','write','0'),
  ('base','ent','mod_by','state','readonly'),
  ('base','ent','mod_date','style','inf'),
  ('base','ent','mod_date','size','18'),
  ('base','ent','mod_date','subframe','2 99'),
  ('base','ent','mod_date','optional','1'),
  ('base','ent','mod_date','write','0'),
  ('base','ent','mod_date','state','readonly'),
  ('base','ent','ent_name','focus','true'),
  ('base','ent','id','display','1'),
  ('base','ent','ent_type','display','2'),
  ('base','ent','ent_name','display','3'),
  ('base','ent','fir_name','display','4'),
  ('base','ent','born_date','display','5'),
  ('base','ent_v','std_name','style','ent'),
  ('base','ent_v','std_name','size','18'),
  ('base','ent_v','std_name','subframe','1 8'),
  ('base','ent_v','std_name','optional','1'),
  ('base','ent_v','std_name','state','readonly'),
  ('base','ent_v','std_name','write','0'),
  ('base','ent_v','frm_name','style','ent'),
  ('base','ent_v','frm_name','size','18'),
  ('base','ent_v','frm_name','subframe','2 8'),
  ('base','ent_v','frm_name','optional','1'),
  ('base','ent_v','frm_name','state','readonly'),
  ('base','ent_v','frm_name','write','0'),
  ('base','ent_v','age','style','ent'),
  ('base','ent_v','age','size','4'),
  ('base','ent_v','age','subframe','3 8'),
  ('base','ent_v','age','optional','1'),
  ('base','ent_v','age','state','readonly'),
  ('base','ent_v','age','write','0'),
  ('base','ent_v','cas_name','style','ent'),
  ('base','ent_v','cas_name','size','10'),
  ('base','ent_v','cas_name','subframe','1 9'),
  ('base','ent_v','cas_name','optional','1'),
  ('base','ent_v','cas_name','state','readonly'),
  ('base','ent_v','cas_name','write','0'),
  ('base','ent_v','giv_name','style','ent'),
  ('base','ent_v','giv_name','size','10'),
  ('base','ent_v','giv_name','subframe','2 9'),
  ('base','ent_v','giv_name','optional','1'),
  ('base','ent_v','giv_name','state','readonly'),
  ('base','ent_v','giv_name','write','0'),
  ('base','ent_v_pub','id','style','ent'),
  ('base','ent_v_pub','id','size','6'),
  ('base','ent_v_pub','id','subframe','0 1'),
  ('base','ent_v_pub','id','hide','1'),
  ('base','ent_v_pub','id','write','0'),
  ('base','ent_v_pub','id','justify','r'),
  ('base','ent_v_pub','name','style','ent'),
  ('base','ent_v_pub','name','size','40'),
  ('base','ent_v_pub','name','subframe','1 1 2'),
  ('base','ent_v_pub','name','state','readonly'),
  ('base','ent_v_pub','type','style','ent'),
  ('base','ent_v_pub','type','size','2'),
  ('base','ent_v_pub','type','subframe','1 2'),
  ('base','ent_v_pub','type','state','readonly'),
  ('base','ent_v_pub','username','style','ent'),
  ('base','ent_v_pub','username','size','12'),
  ('base','ent_v_pub','username','subframe','2 2'),
  ('base','ent_v_pub','username','state','readonly'),
  ('base','ent_v_pub','activ','style','chk'),
  ('base','ent_v_pub','activ','size','2'),
  ('base','ent_v_pub','activ','subframe','1 5'),
  ('base','ent_v_pub','activ','state','readonly'),
  ('base','ent_v_pub','activ','initial','t'),
  ('base','ent_v_pub','activ','onvalue','t'),
  ('base','ent_v_pub','activ','offvalue','f'),
  ('base','ent_v_pub','crt_date','style','ent'),
  ('base','ent_v_pub','crt_date','size','20'),
  ('base','ent_v_pub','crt_date','subframe','1 6'),
  ('base','ent_v_pub','crt_date','optional','1'),
  ('base','ent_v_pub','crt_date','state','readonly'),
  ('base','ent_v_pub','crt_date','write','0'),
  ('base','ent_v_pub','crt_by','style','ent'),
  ('base','ent_v_pub','crt_by','size','10'),
  ('base','ent_v_pub','crt_by','subframe','2 6'),
  ('base','ent_v_pub','crt_by','optional','1'),
  ('base','ent_v_pub','crt_by','state','readonly'),
  ('base','ent_v_pub','crt_by','write','0'),
  ('base','ent_v_pub','mod_date','style','ent'),
  ('base','ent_v_pub','mod_date','size','20'),
  ('base','ent_v_pub','mod_date','subframe','3 6'),
  ('base','ent_v_pub','mod_date','optional','1'),
  ('base','ent_v_pub','mod_date','state','readonly'),
  ('base','ent_v_pub','mod_date','write','0'),
  ('base','ent_v_pub','mod_by','style','ent'),
  ('base','ent_v_pub','mod_by','size','10'),
  ('base','ent_v_pub','mod_by','subframe','4 6'),
  ('base','ent_v_pub','mod_by','optional','1'),
  ('base','ent_v_pub','mod_by','state','readonly'),
  ('base','ent_v_pub','mod_by','write','0'),
  ('base','ent_v_pub','ent_name','focus','true'),
  ('base','ent_link','org','style','ent'),
  ('base','ent_link','org','size','6'),
  ('base','ent_link','org','subframe','1 1'),
  ('base','ent_link','org','justify','r'),
  ('base','ent_link','mem','style','ent'),
  ('base','ent_link','mem','size','6'),
  ('base','ent_link','mem','subframe','1 2'),
  ('base','ent_link','mem','justify','r'),
  ('base','ent_link','role','style','ent'),
  ('base','ent_link','role','size','30'),
  ('base','ent_link','role','subframe','1 3'),
  ('base','ent_link','role','special','exs'),
  ('base','ent_link','org_id','focus','true'),
  ('base','ent_link_v','org_name','style','ent'),
  ('base','ent_link_v','org_name','size','30'),
  ('base','ent_link_v','org_name','subframe',''),
  ('base','ent_link_v','org_name','depend','org_id'),
  ('base','ent_link_v','org_name','title',':'),
  ('base','ent_link_v','org_name','inside','org_id'),
  ('base','ent_link_v','mem_name','style','ent'),
  ('base','ent_link_v','mem_name','size','30'),
  ('base','ent_link_v','mem_name','subframe',''),
  ('base','ent_link_v','mem_name','depend','mem_id'),
  ('base','ent_link_v','mem_name','title',':'),
  ('base','ent_link_v','mem_name','inside','mem_id'),
  ('base','parm_v','module','style','ent'),
  ('base','parm_v','module','size','12'),
  ('base','parm_v','module','subframe','1 1'),
  ('base','parm_v','module','special','exs'),
  ('base','parm_v','parm','style','ent'),
  ('base','parm_v','parm','size','24'),
  ('base','parm_v','parm','subframe','2 1'),
  ('base','parm_v','type','style','pdm'),
  ('base','parm_v','type','size','6'),
  ('base','parm_v','type','subframe','1 2'),
  ('base','parm_v','type','initial','text'),
  ('base','parm_v','value','style','ent'),
  ('base','parm_v','value','size','24'),
  ('base','parm_v','value','subframe','2 2'),
  ('base','parm_v','value','special','edw'),
  ('base','parm_v','value','hot','1'),
  ('base','parm_v','cmt','style','ent'),
  ('base','parm_v','cmt','size','50'),
  ('base','parm_v','cmt','subframe','1 3 2'),
  ('base','parm_v','cmt','special','edw'),
  ('base','parm_v','crt_by','style','ent'),
  ('base','parm_v','crt_by','size','10'),
  ('base','parm_v','crt_by','subframe','1 98'),
  ('base','parm_v','crt_by','optional','1'),
  ('base','parm_v','crt_by','write','0'),
  ('base','parm_v','crt_by','state','readonly'),
  ('base','parm_v','crt_date','style','inf'),
  ('base','parm_v','crt_date','size','18'),
  ('base','parm_v','crt_date','subframe','2 98'),
  ('base','parm_v','crt_date','optional','1'),
  ('base','parm_v','crt_date','write','0'),
  ('base','parm_v','crt_date','state','readonly'),
  ('base','parm_v','mod_by','style','ent'),
  ('base','parm_v','mod_by','size','10'),
  ('base','parm_v','mod_by','subframe','1 99'),
  ('base','parm_v','mod_by','optional','1'),
  ('base','parm_v','mod_by','write','0'),
  ('base','parm_v','mod_by','state','readonly'),
  ('base','parm_v','mod_date','style','inf'),
  ('base','parm_v','mod_date','size','18'),
  ('base','parm_v','mod_date','subframe','2 99'),
  ('base','parm_v','mod_date','optional','1'),
  ('base','parm_v','mod_date','write','0'),
  ('base','parm_v','mod_date','state','readonly'),
  ('base','parm_v','module','focus','true'),
  ('base','parm_v','module','display','1'),
  ('base','parm_v','parm','display','2'),
  ('base','parm_v','type','display','3'),
  ('base','parm_v','cmt','display','5'),
  ('base','parm_v','value','display','4'),
  ('base','priv','grantee','style','ent'),
  ('base','priv','grantee','size','12'),
  ('base','priv','grantee','subframe','0 0'),
  ('base','priv','grantee','state','readonly'),
  ('base','priv','priv','style','ent'),
  ('base','priv','priv','size','12'),
  ('base','priv','priv','subframe','1 0'),
  ('base','priv','priv','special','exs'),
  ('base','priv','level','style','pdm'),
  ('base','priv','level','size','6'),
  ('base','priv','level','subframe','2 0'),
  ('base','priv','level','initial','user'),
  ('base','priv','cmt','style','ent'),
  ('base','priv','cmt','size','50'),
  ('base','priv','cmt','subframe','0 1 3'),
  ('base','priv','priv','focus','true'),
  ('base','priv_v','std_name','style','ent'),
  ('base','priv_v','std_name','size','24'),
  ('base','priv_v','std_name','subframe','0 2'),
  ('base','priv_v','std_name','optional','1'),
  ('base','priv_v','std_name','state','disabled'),
  ('base','priv_v','std_name','write','0'),
  ('base','priv_v','priv_level','style','ent'),
  ('base','priv_v','priv_level','size','24'),
  ('base','priv_v','priv_level','subframe','1 2'),
  ('base','priv_v','priv_level','optional','1'),
  ('base','priv_v','priv_level','state','disabled'),
  ('base','priv_v','priv_level','write','0'),
  ('base','priv_v','priv_list','style','ent'),
  ('base','priv_v','priv_list','size','48'),
  ('base','priv_v','priv_list','subframe','0 3 2'),
  ('base','priv_v','priv_list','optional','1'),
  ('base','priv_v','priv_list','state','disabled'),
  ('base','priv_v','priv_list','write','0'),
  ('mychips','contracts','domain','style','ent'),
  ('mychips','contracts','domain','size','20'),
  ('mychips','contracts','domain','subframe','1 1'),
  ('mychips','contracts','version','style','ent'),
  ('mychips','contracts','version','size','3'),
  ('mychips','contracts','version','subframe','2 1'),
  ('mychips','contracts','version','justify','r'),
  ('mychips','contracts','published','style','ent'),
  ('mychips','contracts','published','size','14'),
  ('mychips','contracts','published','subframe','3 1'),
  ('mychips','contracts','published','state','readonly'),
  ('mychips','contracts','published','write','0'),
  ('mychips','contracts','name','style','ent'),
  ('mychips','contracts','name','size','30'),
  ('mychips','contracts','name','subframe','1 2 2'),
  ('mychips','contracts','language','style','ent'),
  ('mychips','contracts','language','size','4'),
  ('mychips','contracts','language','subframe','3 2'),
  ('mychips','contracts','digest','style','ent'),
  ('mychips','contracts','digest','size','20'),
  ('mychips','contracts','digest','subframe','3 3'),
  ('mychips','contracts','digest','state','readonly'),
  ('mychips','contracts','digest','write','0'),
  ('mychips','contracts','text','style','mle'),
  ('mychips','contracts','text','size','80'),
  ('mychips','contracts','text','subframe','1 4 4'),
  ('mychips','contracts','text','special','edw'),
  ('mychips','contracts','text','state','readonly'),
  ('mychips','contracts','crt_by','style','ent'),
  ('mychips','contracts','crt_by','size','10'),
  ('mychips','contracts','crt_by','subframe','1 98'),
  ('mychips','contracts','crt_by','optional','1'),
  ('mychips','contracts','crt_by','write','0'),
  ('mychips','contracts','crt_by','state','readonly'),
  ('mychips','contracts','crt_date','style','inf'),
  ('mychips','contracts','crt_date','size','18'),
  ('mychips','contracts','crt_date','subframe','2 98'),
  ('mychips','contracts','crt_date','optional','1'),
  ('mychips','contracts','crt_date','write','0'),
  ('mychips','contracts','crt_date','state','readonly'),
  ('mychips','contracts','mod_by','style','ent'),
  ('mychips','contracts','mod_by','size','10'),
  ('mychips','contracts','mod_by','subframe','1 99'),
  ('mychips','contracts','mod_by','optional','1'),
  ('mychips','contracts','mod_by','write','0'),
  ('mychips','contracts','mod_by','state','readonly'),
  ('mychips','contracts','mod_date','style','inf'),
  ('mychips','contracts','mod_date','size','18'),
  ('mychips','contracts','mod_date','subframe','2 99'),
  ('mychips','contracts','mod_date','optional','1'),
  ('mychips','contracts','mod_date','write','0'),
  ('mychips','contracts','mod_date','state','readonly'),
  ('mychips','contracts','domain','focus','true'),
  ('mychips','contracts','domain','display','1'),
  ('mychips','contracts','name','display','2'),
  ('mychips','contracts','version','display','3'),
  ('mychips','contracts','language','display','4'),
  ('mychips','contracts','title','display','7'),
  ('mychips','contracts_v','source','style','ent'),
  ('mychips','contracts_v','source','size','20'),
  ('mychips','contracts_v','source','subframe','1 3 2'),
  ('mychips','paths_v','id','display','1'),
  ('mychips','paths_v','length','display','2'),
  ('mychips','paths_v','path','display','6'),
  ('mychips','paths_v','circuit','display','5'),
  ('mychips','paths_v','cost','display','3'),
  ('mychips','paths_v','min','display','4'),
  ('mychips','peers','peer_ent','style','ent'),
  ('mychips','peers','peer_ent','size','6'),
  ('mychips','peers','peer_ent','subframe','0 20'),
  ('mychips','peers','peer_ent','hide','1'),
  ('mychips','peers','peer_ent','sort','1'),
  ('mychips','peers','peer_ent','write','0'),
  ('mychips','peers','peer_cdi','style','ent'),
  ('mychips','peers','peer_cdi','size','40'),
  ('mychips','peers','peer_cdi','subframe','1 20 2'),
  ('mychips','peers','peer_cdi','template','^[\w\._:/]*$'),
  ('mychips','peers','peer_hid','style','ent'),
  ('mychips','peers','peer_hid','size','40'),
  ('mychips','peers','peer_hid','subframe','3 20 w'),
  ('mychips','peers','peer_inet','style','ent'),
  ('mychips','peers','peer_inet','size','20'),
  ('mychips','peers','peer_inet','subframe','1 21'),
  ('mychips','peers','peer_port','style','ent'),
  ('mychips','peers','peer_port','size','8'),
  ('mychips','peers','peer_port','subframe','2 21'),
  ('mychips','peers','peer_port','justify','r'),
  ('mychips','peers','peer_pub','style','ent'),
  ('mychips','peers','peer_pub','size','20'),
  ('mychips','peers','peer_pub','subframe','1 22 2'),
  ('mychips','peers','peer_pub','special','edw'),
  ('mychips','peers','peer_pub','write','0'),
  ('mychips','peers','peer_cmt','style','mle'),
  ('mychips','peers','peer_cmt','size','80 2'),
  ('mychips','peers','peer_cmt','subframe','1 22 4'),
  ('mychips','peers','crt_by','style','ent'),
  ('mychips','peers','crt_by','size','10'),
  ('mychips','peers','crt_by','subframe','1 98'),
  ('mychips','peers','crt_by','optional','1'),
  ('mychips','peers','crt_by','write','0'),
  ('mychips','peers','crt_by','state','readonly'),
  ('mychips','peers','crt_date','style','inf'),
  ('mychips','peers','crt_date','size','18'),
  ('mychips','peers','crt_date','subframe','2 98'),
  ('mychips','peers','crt_date','optional','1'),
  ('mychips','peers','crt_date','write','0'),
  ('mychips','peers','crt_date','state','readonly'),
  ('mychips','peers','mod_by','style','ent'),
  ('mychips','peers','mod_by','size','10'),
  ('mychips','peers','mod_by','subframe','1 99'),
  ('mychips','peers','mod_by','optional','1'),
  ('mychips','peers','mod_by','write','0'),
  ('mychips','peers','mod_by','state','readonly'),
  ('mychips','peers','mod_date','style','inf'),
  ('mychips','peers','mod_date','size','18'),
  ('mychips','peers','mod_date','subframe','2 99'),
  ('mychips','peers','mod_date','optional','1'),
  ('mychips','peers','mod_date','write','0'),
  ('mychips','peers','mod_date','state','readonly'),
  ('mychips','peers','ent_name','focus','true'),
  ('mychips','peers_v','peer_sock','style','ent'),
  ('mychips','peers_v','peer_sock','size','28'),
  ('mychips','peers_v','peer_sock','subframe','3 21'),
  ('mychips','peers_v','peer_sock','optional','1'),
  ('mychips','peers_v','peer_sock','state','readonly'),
  ('mychips','peers_v','peer_sock','write','0'),
  ('mychips','peers_v','id','display','1'),
  ('mychips','peers_v','ent_name','display','0'),
  ('mychips','peers_v','ent_type','display','5'),
  ('mychips','peers_v','fir_name','display','0'),
  ('mychips','peers_v','born_date','display','6'),
  ('mychips','peers_v','std_name','display','2'),
  ('mychips','peers_v','peer_cdi','display','3'),
  ('mychips','peers_v','peer_sock','display','4'),
  ('mychips','peers_v_flat','id','display','1'),
  ('mychips','peers_v_flat','std_name','display','3'),
  ('mychips','peers_v_flat','peer_cdi','display','2'),
  ('mychips','peers_v_flat','bill_addr','display','4'),
  ('mychips','peers_v_flat','bill_city','display','5'),
  ('mychips','peers_v_flat','bill_state','display','6'),
  ('mychips','peers_v_flat','id','sort','2'),
  ('mychips','peers_v_flat','std_name','sort','1'),
  ('mychips','users','user_ent','style','ent'),
  ('mychips','users','user_ent','size','6'),
  ('mychips','users','user_ent','subframe','0 10'),
  ('mychips','users','user_ent','sort','1'),
  ('mychips','users','user_ent','write','0'),
  ('mychips','users','user_ent','hide','1'),
  ('mychips','users','user_stat','style','pdm'),
  ('mychips','users','user_stat','size','10'),
  ('mychips','users','user_stat','subframe','1 10'),
  ('mychips','users','user_stat','initial','act'),
  ('mychips','users','host_id','style','ent'),
  ('mychips','users','host_id','size','40'),
  ('mychips','users','host_id','subframe','2 10'),
  ('mychips','users','user_inet','style','ent'),
  ('mychips','users','user_inet','size','40'),
  ('mychips','users','user_inet','subframe','1 11'),
  ('mychips','users','user_port','style','ent'),
  ('mychips','users','user_port','size','8'),
  ('mychips','users','user_port','subframe','2 11'),
  ('mychips','users','user_port','justify','r'),
  ('mychips','users','user_cmt','style','mle'),
  ('mychips','users','user_cmt','size','80 2'),
  ('mychips','users','user_cmt','subframe','1 12 4'),
  ('mychips','users','crt_by','style','ent'),
  ('mychips','users','crt_by','size','10'),
  ('mychips','users','crt_by','subframe','1 98'),
  ('mychips','users','crt_by','optional','1'),
  ('mychips','users','crt_by','write','0'),
  ('mychips','users','crt_by','state','readonly'),
  ('mychips','users','crt_date','style','inf'),
  ('mychips','users','crt_date','size','18'),
  ('mychips','users','crt_date','subframe','2 98'),
  ('mychips','users','crt_date','optional','1'),
  ('mychips','users','crt_date','write','0'),
  ('mychips','users','crt_date','state','readonly'),
  ('mychips','users','mod_by','style','ent'),
  ('mychips','users','mod_by','size','10'),
  ('mychips','users','mod_by','subframe','1 99'),
  ('mychips','users','mod_by','optional','1'),
  ('mychips','users','mod_by','write','0'),
  ('mychips','users','mod_by','state','readonly'),
  ('mychips','users','mod_date','style','inf'),
  ('mychips','users','mod_date','size','18'),
  ('mychips','users','mod_date','subframe','2 99'),
  ('mychips','users','mod_date','optional','1'),
  ('mychips','users','mod_date','write','0'),
  ('mychips','users','mod_date','state','readonly'),
  ('mychips','users','ent_name','focus','true'),
  ('mychips','users_v','user_sock','style','ent'),
  ('mychips','users_v','user_sock','size','28'),
  ('mychips','users_v','user_sock','subframe','3 11'),
  ('mychips','users_v','user_sock','optional','1'),
  ('mychips','users_v','user_sock','state','readonly'),
  ('mychips','users_v','user_sock','write','0'),
  ('mychips','users_v','peer_sock','style','ent'),
  ('mychips','users_v','peer_sock','size','28'),
  ('mychips','users_v','peer_sock','subframe','3 21'),
  ('mychips','users_v','peer_sock','optional','1'),
  ('mychips','users_v','peer_sock','state','readonly'),
  ('mychips','users_v','peer_sock','write','0'),
  ('mychips','users_v','id','display','1'),
  ('mychips','users_v','ent_name','display','0'),
  ('mychips','users_v','ent_type','display','3'),
  ('mychips','users_v','fir_name','display','0'),
  ('mychips','users_v','born_date','display','6'),
  ('mychips','users_v','std_name','display','2'),
  ('mychips','users_v','user_stat','display','4'),
  ('mychips','users_v','user_sock','display','5'),
  ('mychips','users_v_flat','id','display','1'),
  ('mychips','users_v_flat','std_name','display','3'),
  ('mychips','users_v_flat','bill_addr','display','4'),
  ('mychips','users_v_flat','bill_city','display','5'),
  ('mychips','users_v_flat','bill_state','display','6'),
  ('mychips','users_v_flat','id','sort','2'),
  ('mychips','users_v_flat','std_name','sort','1');

insert into wm.column_native (cnt_sch,cnt_tab,cnt_col,nat_sch,nat_tab,nat_col,nat_exp,pkey) values
  ('wm','depends_v','depend','wm','depends_v','depend','f','f'),
  ('base','ent_audit','a_reason','base','ent_audit','a_reason','f','f'),
  ('base','parm_audit','a_reason','base','parm_audit','a_reason','f','f'),
  ('base','parm','v_int','base','parm','v_int','f','f'),
  ('mychips','users_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('mychips','peers_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('base','addr_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('base','addr_v_flat','phys_pcode','base','addr_v_flat','phys_pcode','f','f'),
  ('mychips','users_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('mychips','peers_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('base','addr_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('base','country','cur_code','base','country','cur_code','f','f'),
  ('wm','column_style','sw_value','wm','column_style','sw_value','f','f'),
  ('wm','table_style','sw_value','wm','table_style','sw_value','f','f'),
  ('base','country','com_name','base','country','com_name','f','f'),
  ('wm','depends_v','od_typ','wm','depends_v','od_typ','f','f'),
  ('mychips','users_v_flat','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','peers_v_flat','giv_name','base','ent_v','giv_name','f','f'),
  ('base','ent_v','giv_name','base','ent_v','giv_name','f','f'),
  ('base','addr_v_flat','phys_state','base','addr_v_flat','phys_state','f','f'),
  ('wm','depends_v','od_release','wm','depends_v','od_release','f','f'),
  ('base','addr_v_flat','phys_city','base','addr_v_flat','phys_city','f','f'),
  ('mychips','chits','chit_type','mychips','chits','chit_type','f','f'),
  ('mychips','users_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('mychips','peers_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('base','comm_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('mychips','peers_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('mychips','users_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('base','addr_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('wm','objects_v_depth','mod_date','wm','objects','mod_date','f','f'),
  ('mychips','peers_v_flat','mod_date','mychips','peers','mod_date','f','f'),
  ('mychips','users_v_flat','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','peers','mod_date','mychips','peers','mod_date','f','f'),
  ('mychips','users','mod_date','mychips','users','mod_date','f','f'),
  ('base','ent_v_pub','mod_date','base','ent','mod_date','f','f'),
  ('base','comm_v','mod_date','base','comm','mod_date','f','f'),
  ('mychips','chits','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','contracts_v','mod_date','mychips','contracts','mod_date','f','f'),
  ('base','ent_v','mod_date','base','ent','mod_date','f','f'),
  ('base','ent','mod_date','base','ent','mod_date','f','f'),
  ('mychips','tallies','mod_date','mychips','tallies','mod_date','f','f'),
  ('wm','objects','mod_date','wm','objects','mod_date','f','f'),
  ('mychips','contracts','mod_date','mychips','contracts','mod_date','f','f'),
  ('mychips','tokens','mod_date','mychips','tokens','mod_date','f','f'),
  ('base','comm','mod_date','base','comm','mod_date','f','f'),
  ('wylib','data_v','mod_date','wylib','data','mod_date','f','f'),
  ('wylib','data','mod_date','wylib','data','mod_date','f','f'),
  ('base','parm_v','mod_date','base','parm','mod_date','f','f'),
  ('base','token','mod_date','base','token','mod_date','f','f'),
  ('base','ent_link_v','mod_date','base','ent_link','mod_date','f','f'),
  ('base','parm','mod_date','base','parm','mod_date','f','f'),
  ('base','ent_link','mod_date','base','ent_link','mod_date','f','f'),
  ('base','addr','mod_date','base','addr','mod_date','f','f'),
  ('wm','objects_v','mod_date','wm','objects','mod_date','f','f'),
  ('mychips','tokens_v','mod_date','mychips','tokens','mod_date','f','f'),
  ('base','token_v','mod_date','base','token','mod_date','f','f'),
  ('base','addr_v','mod_date','base','addr','mod_date','f','f'),
  ('base','comm_v','comm_inact','base','comm','comm_inact','f','f'),
  ('base','comm','comm_inact','base','comm','comm_inact','f','f'),
  ('base','language','eng_name','base','language','eng_name','f','f'),
  ('base','country','cur_name','base','country','cur_name','f','f'),
  ('wm','objects','deps','wm','objects','deps','f','f'),
  ('wm','objects_v','deps','wm','objects','deps','f','f'),
  ('mychips','peers_v_flat','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v_flat','ent_type','base','ent','ent_type','f','f'),
  ('base','ent_v','ent_type','base','ent','ent_type','f','f'),
  ('base','ent_v_pub','ent_type','base','ent','ent_type','f','f'),
  ('base','ent','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v_flat','peer_sock','mychips','users_v','peer_sock','f','f'),
  ('mychips','peers_v_flat','peer_sock','mychips','peers_v','peer_sock','f','f'),
  ('wm','objects_v_depth','object','wm','objects_v','object','f','f'),
  ('wm','objects_v','object','wm','objects_v','object','f','f'),
  ('wm','depends_v','object','wm','depends_v','object','f','f'),
  ('mychips','peers_v_flat','marital','base','ent','marital','f','f'),
  ('mychips','users_v_flat','marital','base','ent','marital','f','f'),
  ('base','ent_v','marital','base','ent','marital','f','f'),
  ('base','ent','marital','base','ent','marital','f','f'),
  ('mychips','users_v_flat','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','peers_v_flat','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','peers','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','tokens_v','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('base','addr','addr_type','base','addr','addr_type','f','f'),
  ('base','addr_v','addr_type','base','addr','addr_type','f','f'),
  ('wm','value_text','help','wm','value_text','help','f','f'),
  ('wm','column_text','help','wm','column_text','help','f','f'),
  ('wm','message_text','help','wm','message_text','help','f','f'),
  ('wm','table_text','help','wm','table_text','help','f','f'),
  ('base','parm','v_date','base','parm','v_date','f','f'),
  ('wm','depends_v','od_nam','wm','depends_v','od_nam','f','f'),
  ('mychips','users_v_flat','conn_pub','base','ent','conn_pub','f','f'),
  ('base','ent_v','conn_pub','base','ent','conn_pub','f','f'),
  ('base','ent','conn_pub','base','ent','conn_pub','f','f'),
  ('base','ent_link','supr_path','base','ent_link','supr_path','f','f'),
  ('base','ent_link_v','supr_path','base','ent_link','supr_path','f','f'),
  ('mychips','users_v_flat','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','peers_v_flat','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','peers','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','users','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v_flat','user_stat','mychips','users','user_stat','f','f'),
  ('wylib','data','component','wylib','data','component','f','f'),
  ('wylib','data_v','component','wylib','data','component','f','f'),
  ('mychips','tokens','allows','mychips','tokens','allows','f','f'),
  ('mychips','tokens_v','allows','mychips','tokens','allows','f','f'),
  ('base','token_v','allows','base','token','allows','f','f'),
  ('base','token','allows','base','token','allows','f','f'),
  ('mychips','tallies','bal_target','mychips','tallies','bal_target','f','f'),
  ('wm','objects_v_depth','module','wm','objects','module','f','f'),
  ('wm','objects','module','wm','objects','module','f','f'),
  ('wm','objects_v','module','wm','objects','module','f','f'),
  ('wm','depends_v','cycle','wm','depends_v','cycle','f','f'),
  ('base','comm_v_flat','pager_comm','base','comm_v_flat','pager_comm','f','f'),
  ('mychips','peers','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','users_v_flat','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','peers_v_flat','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','tokens_v','exp_date','mychips','tokens','exp_date','f','f'),
  ('mychips','tokens','exp_date','mychips','tokens','exp_date','f','f'),
  ('base','ent_v','country','base','ent','country','f','f'),
  ('mychips','peers_v_flat','country','base','ent','country','f','f'),
  ('mychips','users_v_flat','country','base','ent','country','f','f'),
  ('base','token','used','base','token','used','f','f'),
  ('base','addr','country','base','addr','country','f','f'),
  ('mychips','tokens_v','used','mychips','tokens','used','f','f'),
  ('base','addr_v','country','base','addr','country','f','f'),
  ('base','token_v','used','base','token','used','f','f'),
  ('base','ent','country','base','ent','country','f','f'),
  ('mychips','tokens','used','mychips','tokens','used','f','f'),
  ('base','priv','level','base','priv','level','f','f'),
  ('base','priv_v','level','base','priv','level','f','f'),
  ('wm','objects_v_depth','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects_v','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects','drp_sql','wm','objects','drp_sql','f','f'),
  ('base','addr_v','city','base','addr','city','f','f'),
  ('base','addr','city','base','addr','city','f','f'),
  ('base','addr_v','state','base','addr','state','f','f'),
  ('base','addr','state','base','addr','state','f','f'),
  ('mychips','chits','units','mychips','chits','units','f','f'),
  ('base','parm_v','value','base','parm_v','value','f','f'),
  ('base','language','fra_name','base','language','fra_name','f','f'),
  ('base','ent_v_pub','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent_v','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v_flat','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','peers_v_flat','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent','ent_inact','base','ent','ent_inact','f','f'),
  ('base','comm_v','comm_type','base','comm','comm_type','f','f'),
  ('base','comm','comm_type','base','comm','comm_type','f','f'),
  ('mychips','tallies','version','mychips','tallies','version','f','f'),
  ('mychips','users_v_flat','age','base','ent_v','age','f','f'),
  ('base','ent_v','age','base','ent_v','age','f','f'),
  ('base','token_v','valid','base','token_v','valid','f','f'),
  ('mychips','tokens_v','valid','mychips','tokens_v','valid','f','f'),
  ('base','priv_v','priv_list','base','priv_v','priv_list','f','f'),
  ('mychips','tokens','token_cmt','mychips','tokens','token_cmt','f','f'),
  ('mychips','tokens_v','token_cmt','mychips','tokens','token_cmt','f','f'),
  ('base','comm_v','comm_spec','base','comm','comm_spec','f','f'),
  ('base','comm','comm_spec','base','comm','comm_spec','f','f'),
  ('base','ent_audit','a_by','base','ent_audit','a_by','f','f'),
  ('base','parm_audit','a_by','base','parm_audit','a_by','f','f'),
  ('base','comm_v_flat','other_comm','base','comm_v_flat','other_comm','f','f'),
  ('base','addr_v_flat','phys_addr','base','addr_v_flat','phys_addr','f','f'),
  ('base','ent_link_v','mem_name','base','ent_link_v','mem_name','f','f'),
  ('wm','objects_v_depth','deps','wm','objects','deps','f','f'),
  ('mychips','tallies','cr_limit','mychips','tallies','cr_limit','f','f'),
  ('base','addr_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('mychips','users_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('mychips','peers_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('wm','column_native','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wylib','data_v','own_name','wylib','data_v','own_name','f','f'),
  ('wm','column_native','nat_tab','wm','column_native','nat_tab','f','f'),
  ('base','priv','cmt','base','priv','cmt','f','f'),
  ('base','parm_v','cmt','base','parm','cmt','f','f'),
  ('base','parm','cmt','base','parm','cmt','f','f'),
  ('base','priv_v','cmt','base','priv','cmt','f','f'),
  ('base','comm_v','comm_prim','base','comm_v','comm_prim','f','f'),
  ('base','comm','comm_prim','base','comm','comm_prim','f','f'),
  ('mychips','peers','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','users_v_flat','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','peers_v_flat','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','contracts_v','source','mychips','contracts_v','source','f','f'),
  ('wm','objects_v_depth','source','wm','objects','source','f','f'),
  ('wm','objects_v','source','wm','objects','source','f','f'),
  ('wm','objects','source','wm','objects','source','f','f'),
  ('mychips','users','user_inet','mychips','users','user_inet','f','f'),
  ('mychips','users_v_flat','user_inet','mychips','users','user_inet','f','f'),
  ('mychips','tokens_v','user_inet','mychips','users','user_inet','f','f'),
  ('base','country','iso_3','base','country','iso_3','f','f'),
  ('wylib','data_v','data','wylib','data','data','f','f'),
  ('wylib','data','data','wylib','data','data','f','f'),
  ('mychips','tallies','contract','mychips','tallies','contract','f','f'),
  ('base','country','capital','base','country','capital','f','f'),
  ('wm','objects_v_depth','mod_ver','wm','objects','mod_ver','f','f'),
  ('base','addr_v','pcode','base','addr','pcode','f','f'),
  ('wm','objects_v','mod_ver','wm','objects','mod_ver','f','f'),
  ('base','addr','pcode','base','addr','pcode','f','f'),
  ('wm','objects','mod_ver','wm','objects','mod_ver','f','f'),
  ('base','ent_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v_flat','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','peers_v_flat','ent_cmt','base','ent','ent_cmt','f','f'),
  ('base','ent','ent_cmt','base','ent','ent_cmt','f','f'),
  ('wm','objects_v_depth','grants','wm','objects','grants','f','f'),
  ('wm','objects_v','grants','wm','objects','grants','f','f'),
  ('wm','objects','grants','wm','objects','grants','f','f'),
  ('mychips','tallies','user_sig','mychips','tallies','user_sig','f','f'),
  ('base','addr_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('mychips','peers_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('mychips','users_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('base','parm','v_boolean','base','parm','v_boolean','f','f'),
  ('mychips','tallies','part_sig','mychips','tallies','part_sig','f','f'),
  ('mychips','users_v_flat','user_sock','mychips','users_v','user_sock','f','f'),
  ('mychips','peers_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('mychips','users_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('base','comm_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('mychips','tallies','dr_limit','mychips','tallies','dr_limit','f','f'),
  ('mychips','confirms','conf_id','mychips','confirms','conf_id','f','f'),
  ('base','ent','ent_name','base','ent','ent_name','f','f'),
  ('mychips','peers_v_flat','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v_flat','ent_name','base','ent','ent_name','f','f'),
  ('base','ent_v','ent_name','base','ent','ent_name','f','f'),
  ('base','addr','addr_prim','base','addr','addr_prim','f','f'),
  ('base','addr_v','addr_prim','base','addr_v','addr_prim','f','f'),
  ('mychips','tallies','status','mychips','tallies','status','f','f'),
  ('mychips','peers','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','peers_v_flat','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','users_v_flat','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('base','ent_v','crt_date','base','ent','crt_date','f','f'),
  ('mychips','contracts_v','crt_date','mychips','contracts','crt_date','f','f'),
  ('mychips','peers','crt_date','mychips','peers','crt_date','f','f'),
  ('mychips','chits','crt_date','mychips','chits','crt_date','f','f'),
  ('base','ent_v_pub','crt_date','base','ent','crt_date','f','f'),
  ('base','comm_v','crt_date','base','comm','crt_date','f','f'),
  ('mychips','users','crt_date','mychips','users','crt_date','f','f'),
  ('wm','releases','crt_date','wm','releases','crt_date','f','f'),
  ('mychips','peers_v_flat','crt_date','mychips','peers','crt_date','f','f'),
  ('mychips','users_v_flat','crt_date','mychips','users','crt_date','f','f'),
  ('wm','objects_v_depth','crt_date','wm','objects','crt_date','f','f'),
  ('mychips','tokens_v','crt_date','mychips','tokens','crt_date','f','f'),
  ('base','token_v','crt_date','base','token','crt_date','f','f'),
  ('base','addr_v','crt_date','base','addr','crt_date','f','f'),
  ('base','addr','crt_date','base','addr','crt_date','f','f'),
  ('wm','objects_v','crt_date','wm','objects','crt_date','f','f'),
  ('base','ent_link','crt_date','base','ent_link','crt_date','f','f'),
  ('base','ent_link_v','crt_date','base','ent_link','crt_date','f','f'),
  ('base','parm','crt_date','base','parm','crt_date','f','f'),
  ('base','token','crt_date','base','token','crt_date','f','f'),
  ('base','parm_v','crt_date','base','parm','crt_date','f','f'),
  ('wylib','data','crt_date','wylib','data','crt_date','f','f'),
  ('base','comm','crt_date','base','comm','crt_date','f','f'),
  ('wylib','data_v','crt_date','wylib','data','crt_date','f','f'),
  ('mychips','tokens','crt_date','mychips','tokens','crt_date','f','f'),
  ('mychips','contracts','crt_date','mychips','contracts','crt_date','f','f'),
  ('mychips','tallies','crt_date','mychips','tallies','crt_date','f','f'),
  ('wm','objects','crt_date','wm','objects','crt_date','f','f'),
  ('base','ent','crt_date','base','ent','crt_date','f','f'),
  ('mychips','tallies','tally_date','mychips','tallies','tally_date','f','f'),
  ('base','parm','v_float','base','parm','v_float','f','f'),
  ('base','ent_audit','a_date','base','ent_audit','a_date','f','f'),
  ('base','parm_audit','a_date','base','parm_audit','a_date','f','f'),
  ('mychips','chits','chit_guid','mychips','chits','chit_guid','f','f'),
  ('base','addr_v_flat','mail_country','base','addr_v_flat','mail_country','f','f'),
  ('base','ent_v','proxy','base','ent','proxy','f','f'),
  ('mychips','peers_v_flat','proxy','base','ent','proxy','f','f'),
  ('mychips','users_v_flat','proxy','base','ent','proxy','f','f'),
  ('base','ent','proxy','base','ent','proxy','f','f'),
  ('base','token_v','expires','base','token','expires','f','f'),
  ('base','token','expires','base','token','expires','f','f'),
  ('base','addr_v_flat','mail_state','base','addr_v_flat','mail_state','f','f'),
  ('mychips','users_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('mychips','peers_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('base','comm_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('wm','message_text','title','wm','message_text','title','f','f'),
  ('base','ent','title','base','ent','title','f','f'),
  ('mychips','contracts','title','mychips','contracts','title','f','f'),
  ('wm','table_text','title','wm','table_text','title','f','f'),
  ('mychips','users_v_flat','title','base','ent','title','f','f'),
  ('mychips','peers_v_flat','title','base','ent','title','f','f'),
  ('mychips','contracts_v','title','mychips','contracts','title','f','f'),
  ('base','ent_v','title','base','ent','title','f','f'),
  ('wm','value_text','title','wm','value_text','title','f','f'),
  ('wm','column_text','title','wm','column_text','title','f','f'),
  ('wylib','data_v','descr','wylib','data','descr','f','f'),
  ('wylib','data','descr','wylib','data','descr','f','f'),
  ('mychips','peers_v_flat','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','users_v_flat','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','peers','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','peers_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('mychips','users_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('base','addr_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('mychips','tallies','lift_marg','mychips','tallies','lift_marg','f','f'),
  ('wm','depends_v','fpath','wm','depends_v','fpath','f','f'),
  ('mychips','peers_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('mychips','users_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('base','addr_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('base','ent','fir_name','base','ent','fir_name','f','f'),
  ('mychips','peers_v_flat','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v_flat','fir_name','base','ent','fir_name','f','f'),
  ('base','ent_v','fir_name','base','ent','fir_name','f','f'),
  ('mychips','confirms','sum','mychips','confirms','sum','f','f'),
  ('base','parm_audit','a_value','base','parm_audit','a_value','f','f'),
  ('base','ent_audit','a_value','base','ent_audit','a_value','f','f'),
  ('mychips','confirms','signature','mychips','confirms','signature','f','f'),
  ('mychips','chits','signature','mychips','chits','signature','f','f'),
  ('mychips','contracts','published','mychips','contracts','published','f','f'),
  ('mychips','contracts_v','published','mychips','contracts','published','f','f'),
  ('mychips','tokens','token','mychips','tokens','token','f','f'),
  ('base','token','token','base','token','token','f','f'),
  ('base','ent_link_v','org_name','base','ent_link_v','org_name','f','f'),
  ('base','token_v','token','base','token','token','f','f'),
  ('mychips','tokens_v','token','mychips','tokens','token','f','f'),
  ('mychips','contracts','tag','mychips','contracts','tag','f','f'),
  ('mychips','contracts_v','tag','mychips','contracts','tag','f','f'),
  ('mychips','tallies','tally_type','mychips','tallies','tally_type','f','f'),
  ('base','ent','bank','base','ent','bank','f','f'),
  ('mychips','users_v_flat','bank','base','ent','bank','f','f'),
  ('mychips','peers_v_flat','bank','base','ent','bank','f','f'),
  ('base','ent_v','bank','base','ent','bank','f','f'),
  ('base','parm_audit','a_column','base','parm_audit','a_column','f','f'),
  ('base','ent_audit','a_column','base','ent_audit','a_column','f','f'),
  ('base','addr_v_flat','mail_addr','base','addr_v_flat','mail_addr','f','f'),
  ('wm','column_native','nat_exp','wm','column_native','nat_exp','f','f'),
  ('mychips','tallies','request','mychips','tallies','request','f','f'),
  ('mychips','chits','request','mychips','chits','request','f','f'),
  ('mychips','tokens_v','expired','mychips','tokens_v','expired','f','f'),
  ('base','token_v','expired','base','token_v','expired','f','f'),
  ('base','ent_link','role','base','ent_link','role','f','f'),
  ('base','ent_link_v','role','base','ent_link','role','f','f'),
  ('wylib','data','crt_by','wylib','data','crt_by','f','f'),
  ('mychips','tokens','crt_by','mychips','tokens','crt_by','f','f'),
  ('base','comm','crt_by','base','comm','crt_by','f','f'),
  ('wylib','data_v','crt_by','wylib','data','crt_by','f','f'),
  ('mychips','tallies','crt_by','mychips','tallies','crt_by','f','f'),
  ('mychips','contracts','crt_by','mychips','contracts','crt_by','f','f'),
  ('base','ent','crt_by','base','ent','crt_by','f','f'),
  ('base','parm_v','crt_by','base','parm','crt_by','f','f'),
  ('base','addr','crt_by','base','addr','crt_by','f','f'),
  ('mychips','tokens_v','crt_by','mychips','tokens','crt_by','f','f'),
  ('base','addr_v','crt_by','base','addr','crt_by','f','f'),
  ('base','token_v','crt_by','base','token','crt_by','f','f'),
  ('base','ent_link','crt_by','base','ent_link','crt_by','f','f'),
  ('base','token','crt_by','base','token','crt_by','f','f'),
  ('base','ent_link_v','crt_by','base','ent_link','crt_by','f','f'),
  ('base','parm','crt_by','base','parm','crt_by','f','f'),
  ('mychips','users','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','peers_v_flat','crt_by','mychips','peers','crt_by','f','f'),
  ('mychips','users_v_flat','crt_by','mychips','users','crt_by','f','f'),
  ('base','ent_v','crt_by','base','ent','crt_by','f','f'),
  ('mychips','contracts_v','crt_by','mychips','contracts','crt_by','f','f'),
  ('mychips','peers','crt_by','mychips','peers','crt_by','f','f'),
  ('mychips','chits','crt_by','mychips','chits','crt_by','f','f'),
  ('base','ent_v_pub','crt_by','base','ent','crt_by','f','f'),
  ('base','comm_v','crt_by','base','comm','crt_by','f','f'),
  ('mychips','tallies','tally_guid','mychips','tallies','tally_guid','f','f'),
  ('wm','column_native','pkey','wm','column_native','pkey','f','f'),
  ('mychips','chits','pro_quo','mychips','chits','pro_quo','f','f'),
  ('base','parm','v_text','base','parm','v_text','f','f'),
  ('wm','objects','checked','wm','objects','checked','f','f'),
  ('wm','objects_v','checked','wm','objects','checked','f','f'),
  ('wm','objects_v_depth','checked','wm','objects','checked','f','f'),
  ('wylib','data','access','wylib','data','access','f','f'),
  ('wylib','data_v','access','wylib','data','access','f','f'),
  ('mychips','tallies','stock_terms','mychips','tallies','stock_terms','f','f'),
  ('base','country','iana','base','country','iana','f','f'),
  ('mychips','tallies','comment','mychips','tallies','comment','f','f'),
  ('wm','objects','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v_depth','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects','clean','wm','objects','clean','f','f'),
  ('wm','objects_v','clean','wm','objects','clean','f','f'),
  ('wm','objects_v_depth','clean','wm','objects','clean','f','f'),
  ('mychips','peers_v_flat','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v_flat','frm_name','base','ent_v','frm_name','f','f'),
  ('base','ent_v','frm_name','base','ent_v','frm_name','f','f'),
  ('wm','depends_v','path','wm','depends_v','path','f','f'),
  ('base','ent','born_date','base','ent','born_date','f','f'),
  ('base','ent_v','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v_flat','born_date','base','ent','born_date','f','f'),
  ('mychips','peers_v_flat','born_date','base','ent','born_date','f','f'),
  ('base','country','dial_code','base','country','dial_code','f','f'),
  ('base','parm','type','base','parm','type','f','f'),
  ('base','parm_v','type','base','parm','type','f','f'),
  ('wm','objects_v','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects_v_depth','max_rel','wm','objects','max_rel','f','f'),
  ('base','addr_v_flat','mail_pcode','base','addr_v_flat','mail_pcode','f','f'),
  ('wm','table_style','inherit','wm','table_style','inherit','f','f'),
  ('base','addr_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('mychips','peers_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('mychips','users_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('wm','column_native','nat_col','wm','column_native','nat_col','f','f'),
  ('mychips','tokens_v','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v_flat','user_port','mychips','users','user_port','f','f'),
  ('mychips','users','user_port','mychips','users','user_port','f','f'),
  ('wm','objects_v','col_data','wm','objects','col_data','f','f'),
  ('wm','objects','col_data','wm','objects','col_data','f','f'),
  ('wm','objects_v_depth','col_data','wm','objects','col_data','f','f'),
  ('base','ent_v','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','peers_v_flat','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v_flat','cas_name','base','ent_v','cas_name','f','f'),
  ('base','ent','ent_num','base','ent','ent_num','f','f'),
  ('base','ent_v_pub','ent_num','base','ent','ent_num','f','f'),
  ('base','ent_v','ent_num','base','ent','ent_num','f','f'),
  ('mychips','users_v_flat','ent_num','base','ent','ent_num','f','f'),
  ('mychips','chits','memo','mychips','chits','memo','f','f'),
  ('wylib','data_v','name','wylib','data','name','f','f'),
  ('wylib','data','name','wylib','data','name','f','f'),
  ('base','comm_v_flat','fax_comm','base','comm_v_flat','fax_comm','f','f'),
  ('base','language','iso_2','base','language','iso_2','f','f'),
  ('base','comm','comm_cmt','base','comm','comm_cmt','f','f'),
  ('base','comm_v','comm_cmt','base','comm','comm_cmt','f','f'),
  ('mychips','contracts_v','json','mychips','contracts_v','json','f','f'),
  ('mychips','tallies','partner','mychips','tallies','partner','f','f'),
  ('base','addr_v_flat','phys_country','base','addr_v_flat','phys_country','f','f'),
  ('base','comm_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('mychips','peers_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('mychips','users_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('base','language','iso_3b','base','language','iso_3b','f','f'),
  ('base','parm_audit','a_action','base','parm_audit','a_action','f','f'),
  ('base','ent_audit','a_action','base','ent_audit','a_action','f','f'),
  ('base','addr','addr_spec','base','addr','addr_spec','f','f'),
  ('base','addr_v','addr_spec','base','addr','addr_spec','f','f'),
  ('base','ent','gender','base','ent','gender','f','f'),
  ('base','ent_v','gender','base','ent','gender','f','f'),
  ('mychips','users_v_flat','gender','base','ent','gender','f','f'),
  ('mychips','peers_v_flat','gender','base','ent','gender','f','f'),
  ('mychips','confirms','conf_date','mychips','confirms','conf_date','f','f'),
  ('base','addr_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('mychips','users_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('mychips','peers_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('base','ent','tax_id','base','ent','tax_id','f','f'),
  ('base','ent_v','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v_flat','tax_id','base','ent','tax_id','f','f'),
  ('mychips','peers_v_flat','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users','host_id','mychips','users','host_id','f','f'),
  ('mychips','users_v_flat','host_id','mychips','users','host_id','f','f'),
  ('wm','objects_v','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects_v_depth','min_rel','wm','objects','min_rel','f','f'),
  ('mychips','tallies','drop_marg','mychips','tallies','drop_marg','f','f'),
  ('base','comm_v_flat','text_comm','base','comm_v_flat','text_comm','f','f'),
  ('mychips','users','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v_flat','user_cmt','mychips','users','user_cmt','f','f'),
  ('base','ent','pref_name','base','ent','pref_name','f','f'),
  ('base','ent_v','pref_name','base','ent','pref_name','f','f'),
  ('mychips','peers_v_flat','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v_flat','pref_name','base','ent','pref_name','f','f'),
  ('base','token_v','username','base','ent','username','f','f'),
  ('base','priv_v','username','base','ent','username','f','f'),
  ('base','ent','username','base','ent','username','f','f'),
  ('base','ent','mid_name','base','ent','mid_name','f','f'),
  ('base','ent_v','username','base','ent','username','f','f'),
  ('base','ent_v','mid_name','base','ent','mid_name','f','f'),
  ('base','ent_v_pub','username','base','ent','username','f','f'),
  ('mychips','peers_v_flat','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v_flat','username','base','ent','username','f','f'),
  ('mychips','users_v_flat','mid_name','base','ent','mid_name','f','f'),
  ('mychips','peers_v_flat','username','base','ent','username','f','f'),
  ('wm','releases','sver_1','wm','releases','sver_1','f','f'),
  ('mychips','contracts','digest','mychips','contracts','digest','f','f'),
  ('mychips','contracts_v','digest','mychips','contracts','digest','f','f'),
  ('mychips','chits','chit_date','mychips','chits','chit_date','f','f'),
  ('wm','objects_v','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects_v_depth','crt_sql','wm','objects','crt_sql','f','f'),
  ('mychips','contracts','sections','mychips','contracts','sections','f','f'),
  ('mychips','contracts_v','sections','mychips','contracts','sections','f','f'),
  ('base','addr_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('base','addr_v_flat','mail_city','base','addr_v_flat','mail_city','f','f'),
  ('mychips','peers_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('mychips','users_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('mychips','tallies','foil_terms','mychips','tallies','foil_terms','f','f'),
  ('mychips','tallies','units_c','mychips','tallies','units_c','f','f'),
  ('mychips','contracts','text','mychips','contracts','text','f','f'),
  ('mychips','contracts_v','text','mychips','contracts','text','f','f'),
  ('wylib','data','owner','wylib','data','owner','f','f'),
  ('wylib','data_v','owner','wylib','data','owner','f','f'),
  ('base','addr_v','addr_cmt','base','addr','addr_cmt','f','f'),
  ('base','addr','addr_cmt','base','addr','addr_cmt','f','f'),
  ('base','priv_v','priv_level','base','priv','priv_level','f','f'),
  ('base','priv','priv_level','base','priv','priv_level','f','f'),
  ('base','addr','mod_by','base','addr','mod_by','f','f'),
  ('mychips','tokens_v','mod_by','mychips','tokens','mod_by','f','f'),
  ('base','addr_v','mod_by','base','addr','mod_by','f','f'),
  ('base','token_v','mod_by','base','token','mod_by','f','f'),
  ('base','ent_link','mod_by','base','ent_link','mod_by','f','f'),
  ('base','token','mod_by','base','token','mod_by','f','f'),
  ('base','ent_link_v','mod_by','base','ent_link','mod_by','f','f'),
  ('base','parm','mod_by','base','parm','mod_by','f','f'),
  ('base','parm_v','mod_by','base','parm','mod_by','f','f'),
  ('wylib','data','mod_by','wylib','data','mod_by','f','f'),
  ('mychips','tokens','mod_by','mychips','tokens','mod_by','f','f'),
  ('base','comm','mod_by','base','comm','mod_by','f','f'),
  ('wylib','data_v','mod_by','wylib','data','mod_by','f','f'),
  ('mychips','tallies','mod_by','mychips','tallies','mod_by','f','f'),
  ('mychips','contracts','mod_by','mychips','contracts','mod_by','f','f'),
  ('base','ent','mod_by','base','ent','mod_by','f','f'),
  ('base','ent_v','mod_by','base','ent','mod_by','f','f'),
  ('mychips','contracts_v','mod_by','mychips','contracts','mod_by','f','f'),
  ('mychips','peers','mod_by','mychips','peers','mod_by','f','f'),
  ('mychips','chits','mod_by','mychips','chits','mod_by','f','f'),
  ('base','ent_v_pub','mod_by','base','ent','mod_by','f','f'),
  ('base','comm_v','mod_by','base','comm','mod_by','f','f'),
  ('mychips','users','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','peers_v_flat','mod_by','mychips','peers','mod_by','f','f'),
  ('mychips','users_v_flat','mod_by','mychips','users','mod_by','f','f'),
  ('base','addr','addr_inact','base','addr','addr_inact','f','f'),
  ('base','addr_v','addr_inact','base','addr','addr_inact','f','f'),
  ('wm','depends_v','depth','wm','depends_v','depth','f','f'),
  ('wm','objects_v_depth','depth','wm','depends_v','depth','f','f'),
  ('base','token_v','std_name','base','ent_v','std_name','f','f'),
  ('base','addr_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','tokens_v','std_name','base','ent_v','std_name','f','f'),
  ('base','priv_v','std_name','base','ent_v','std_name','f','f'),
  ('base','ent_v','std_name','base','ent_v','std_name','f','f'),
  ('base','comm_v','std_name','base','ent_v','std_name','f','f'),
  ('base','ent_v_pub','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v_flat','std_name','base','ent_v','std_name','f','f'),
  ('mychips','peers_v_flat','std_name','base','ent_v','std_name','f','f'),
  ('base','addr','addr_ent','base','addr','addr_ent','f','t'),
  ('base','addr','addr_seq','base','addr','addr_seq','f','t'),
  ('base','addr_prim','prim_seq','base','addr_prim','prim_seq','f','t'),
  ('base','addr_prim','prim_type','base','addr_prim','prim_type','f','t'),
  ('base','addr_prim','prim_ent','base','addr_prim','prim_ent','f','t'),
  ('base','addr_v','addr_seq','base','addr','addr_seq','f','t'),
  ('base','addr_v','addr_ent','base','addr','addr_ent','f','t'),
  ('base','addr_v_flat','id','base','ent','id','f','t'),
  ('base','comm','comm_ent','base','comm','comm_ent','f','t'),
  ('base','comm','comm_seq','base','comm','comm_seq','f','t'),
  ('base','comm_prim','prim_type','base','comm_prim','prim_type','f','t'),
  ('base','comm_prim','prim_ent','base','comm_prim','prim_ent','f','t'),
  ('base','comm_prim','prim_seq','base','comm_prim','prim_seq','f','t'),
  ('base','comm_v','comm_seq','base','comm','comm_seq','f','t'),
  ('base','comm_v','comm_ent','base','comm','comm_ent','f','t'),
  ('base','comm_v_flat','id','base','ent','id','f','t'),
  ('base','country','code','base','country','code','f','t'),
  ('base','ent','id','base','ent','id','f','t'),
  ('base','ent_audit','a_seq','base','ent_audit','a_seq','f','t'),
  ('base','ent_audit','id','base','ent_audit','id','f','t'),
  ('base','ent_link','mem','base','ent_link','mem','f','t'),
  ('base','ent_link','org','base','ent_link','org','f','t'),
  ('base','ent_link_v','mem','base','ent_link','mem','f','t'),
  ('base','ent_link_v','org','base','ent_link','org','f','t'),
  ('base','ent_v','id','base','ent','id','f','t'),
  ('base','ent_v_pub','id','base','ent','id','f','t'),
  ('base','language','code','base','language','code','f','t'),
  ('base','parm','parm','base','parm','parm','f','t'),
  ('base','parm','module','base','parm','module','f','t'),
  ('base','parm_audit','parm','base','parm_audit','parm','f','t'),
  ('base','parm_audit','a_seq','base','parm_audit','a_seq','f','t'),
  ('base','parm_audit','module','base','parm_audit','module','f','t'),
  ('base','parm_v','parm','base','parm','parm','f','t'),
  ('base','parm_v','module','base','parm','module','f','t'),
  ('base','priv','grantee','base','priv','grantee','f','t'),
  ('base','priv','priv','base','priv','priv','f','t'),
  ('base','priv_v','grantee','base','priv','grantee','f','t'),
  ('base','priv_v','priv','base','priv','priv','f','t'),
  ('base','token','token_ent','base','token','token_ent','f','t'),
  ('base','token','token_seq','base','token','token_seq','f','t'),
  ('base','token_v','token_seq','base','token','token_seq','f','t'),
  ('base','token_v','token_ent','base','token','token_ent','f','t'),
  ('mychips','chits','chit_seq','mychips','chits','chit_seq','f','t'),
  ('mychips','chits','chit_ent','mychips','chits','chit_ent','f','t'),
  ('mychips','chits','chit_idx','mychips','chits','chit_idx','f','t'),
  ('mychips','confirms','conf_idx','mychips','confirms','conf_idx','f','t'),
  ('mychips','confirms','conf_seq','mychips','confirms','conf_seq','f','t'),
  ('mychips','confirms','conf_ent','mychips','confirms','conf_ent','f','t'),
  ('mychips','contracts','name','mychips','contracts','name','f','t'),
  ('mychips','contracts','language','mychips','contracts','language','f','t'),
  ('mychips','contracts','domain','mychips','contracts','domain','f','t'),
  ('mychips','contracts','version','mychips','contracts','version','f','t'),
  ('mychips','contracts_v','language','mychips','contracts','language','f','t'),
  ('mychips','contracts_v','domain','mychips','contracts','domain','f','t'),
  ('mychips','contracts_v','name','mychips','contracts','name','f','t'),
  ('mychips','contracts_v','version','mychips','contracts','version','f','t'),
  ('mychips','peers','peer_ent','mychips','peers','peer_ent','f','t'),
  ('mychips','peers_v_flat','id','base','ent','id','f','t'),
  ('mychips','peers_v_flat','peer_ent','mychips','peers','peer_ent','f','t'),
  ('mychips','tallies','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies','tally_seq','mychips','tallies','tally_seq','f','t'),
  ('mychips','tokens','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','tokens','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','tokens_v','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','tokens_v','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','users','user_ent','mychips','users','user_ent','f','t'),
  ('mychips','users_v_flat','peer_ent','mychips','peers','peer_ent','f','t'),
  ('mychips','users_v_flat','id','base','ent','id','f','t'),
  ('mychips','users_v_flat','user_ent','mychips','users','user_ent','f','t'),
  ('wm','column_native','cnt_sch','wm','column_native','cnt_sch','f','t'),
  ('wm','column_native','cnt_col','wm','column_native','cnt_col','f','t'),
  ('wm','column_native','cnt_tab','wm','column_native','cnt_tab','f','t'),
  ('wm','column_style','cs_sch','wm','column_style','cs_sch','f','t'),
  ('wm','column_style','cs_tab','wm','column_style','cs_tab','f','t'),
  ('wm','column_style','sw_name','wm','column_style','sw_name','f','t'),
  ('wm','column_style','cs_col','wm','column_style','cs_col','f','t'),
  ('wm','column_text','language','wm','column_text','language','f','t'),
  ('wm','column_text','ct_col','wm','column_text','ct_col','f','t'),
  ('wm','column_text','ct_tab','wm','column_text','ct_tab','f','t'),
  ('wm','column_text','ct_sch','wm','column_text','ct_sch','f','t'),
  ('wm','message_text','language','wm','message_text','language','f','t'),
  ('wm','message_text','mt_tab','wm','message_text','mt_tab','f','t'),
  ('wm','message_text','code','wm','message_text','code','f','t'),
  ('wm','message_text','mt_sch','wm','message_text','mt_sch','f','t'),
  ('wm','objects','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v','release','wm','releases','release','f','t'),
  ('wm','objects_v_depth','release','wm','releases','release','f','t'),
  ('wm','objects_v_depth','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v_depth','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v_depth','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','releases','release','wm','releases','release','f','t'),
  ('wm','table_style','ts_sch','wm','table_style','ts_sch','f','t'),
  ('wm','table_style','ts_tab','wm','table_style','ts_tab','f','t'),
  ('wm','table_style','sw_name','wm','table_style','sw_name','f','t'),
  ('wm','table_text','tt_tab','wm','table_text','tt_tab','f','t'),
  ('wm','table_text','tt_sch','wm','table_text','tt_sch','f','t'),
  ('wm','table_text','language','wm','table_text','language','f','t'),
  ('wm','value_text','vt_tab','wm','value_text','vt_tab','f','t'),
  ('wm','value_text','vt_col','wm','value_text','vt_col','f','t'),
  ('wm','value_text','vt_sch','wm','value_text','vt_sch','f','t'),
  ('wm','value_text','value','wm','value_text','value','f','t'),
  ('wm','value_text','language','wm','value_text','language','f','t'),
  ('wylib','data','ruid','wylib','data','ruid','f','t'),
  ('wylib','data_v','ruid','wylib','data','ruid','f','t'),
  ('wm','column_meta','nat','wm','column_meta','nat','f','f'),
  ('wm','column_meta','tab','wm','column_meta','tab','f','t'),
  ('wm','column_meta','field','wm','column_data','field','f','f'),
  ('wm','column_meta','obj','wm','column_meta','obj','f','f'),
  ('wm','column_meta','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_meta','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_meta','styles','wm','column_meta','styles','f','f'),
  ('wm','column_meta','is_pkey','wm','column_data','is_pkey','f','f'),
  ('wm','column_meta','col','wm','column_meta','col','f','t'),
  ('wm','column_meta','nonull','wm','column_data','nonull','f','f'),
  ('wm','column_meta','values','wm','column_meta','values','f','f'),
  ('wm','column_meta','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_meta','type','wm','column_data','type','f','f'),
  ('wm','column_meta','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_meta','length','wm','column_data','length','f','f'),
  ('wm','column_meta','def','wm','column_data','def','f','f'),
  ('wm','column_meta','sch','wm','column_meta','sch','f','t'),
  ('wm','column_lang','nat','wm','column_lang','nat','f','f'),
  ('wm','column_lang','tab','wm','column_lang','tab','f','t'),
  ('wm','column_lang','obj','wm','column_lang','obj','f','f'),
  ('wm','column_lang','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_lang','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_lang','system','wm','column_lang','system','f','f'),
  ('wm','column_lang','col','wm','column_lang','col','f','t'),
  ('wm','column_lang','values','wm','column_lang','values','f','f'),
  ('wm','column_lang','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_lang','sch','wm','column_lang','sch','f','t'),
  ('wm','column_lang','title','wm','column_text','title','t','f'),
  ('wm','column_lang','help','wm','column_text','help','t','f'),
  ('wm','column_lang','language','wm','column_text','language','t','f'),
  ('wm','table_meta','tab','wm','column_meta','tab','f','t'),
  ('wm','table_meta','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_meta','obj','wm','table_meta','obj','f','f'),
  ('wm','table_meta','fkeys','wm','table_meta','fkeys','f','f'),
  ('wm','table_meta','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_meta','styles','wm','column_meta','styles','f','f'),
  ('wm','table_meta','system','wm','table_data','system','f','f'),
  ('wm','table_meta','columns','wm','table_meta','columns','f','f'),
  ('wm','table_meta','cols','wm','table_data','cols','f','f'),
  ('wm','table_meta','sch','wm','column_meta','sch','f','t'),
  ('wm','table_meta','pkey','wm','table_data','pkey','t','f'),
  ('mychips','peers_v','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','peers_v','mod_date','mychips','peers','mod_date','f','f'),
  ('mychips','peers_v','ent_type','base','ent','ent_type','f','f'),
  ('mychips','peers_v','peer_sock','mychips','peers_v','peer_sock','f','f'),
  ('mychips','peers_v','marital','base','ent','marital','f','f'),
  ('mychips','peers_v','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','peers_v','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','peers_v','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','peers_v','country','base','ent','country','f','f'),
  ('mychips','peers_v','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','peers_v','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','peers_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','peers_v','ent_name','base','ent','ent_name','f','f'),
  ('mychips','peers_v','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','peers_v','crt_date','mychips','peers','crt_date','f','f'),
  ('mychips','peers_v','proxy','base','ent','proxy','f','f'),
  ('mychips','peers_v','title','base','ent','title','f','f'),
  ('mychips','peers_v','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','peers_v','fir_name','base','ent','fir_name','f','f'),
  ('mychips','peers_v','bank','base','ent','bank','f','f'),
  ('mychips','peers_v','crt_by','mychips','peers','crt_by','f','f'),
  ('mychips','peers_v','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','peers_v','born_date','base','ent','born_date','f','f'),
  ('mychips','peers_v','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','peers_v','gender','base','ent','gender','f','f'),
  ('mychips','peers_v','tax_id','base','ent','tax_id','f','f'),
  ('mychips','peers_v','pref_name','base','ent','pref_name','f','f'),
  ('mychips','peers_v','username','base','ent','username','f','f'),
  ('mychips','peers_v','mid_name','base','ent','mid_name','f','f'),
  ('mychips','peers_v','mod_by','mychips','peers','mod_by','f','f'),
  ('mychips','peers_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','peers_v','peer_ent','mychips','peers','peer_ent','f','f'),
  ('mychips','peers_v','id','base','ent','id','f','t'),
  ('wm','fkey_data','kyf_field','wm','fkey_data','kyf_field','f','f'),
  ('wm','fkey_data','keys','wm','fkey_data','keys','f','f'),
  ('wm','fkey_data','key','wm','fkey_data','key','f','f'),
  ('wm','fkey_data','kyt_tab','wm','fkey_data','kyt_tab','f','f'),
  ('wm','fkey_data','kyf_sch','wm','fkey_data','kyf_sch','f','f'),
  ('wm','fkey_data','conname','wm','fkey_data','conname','f','t'),
  ('wm','fkey_data','kyt_field','wm','fkey_data','kyt_field','f','f'),
  ('wm','fkey_data','kyf_col','wm','fkey_data','kyf_col','f','f'),
  ('wm','fkey_data','kyt_col','wm','fkey_data','kyt_col','f','f'),
  ('wm','fkey_data','kyt_sch','wm','fkey_data','kyt_sch','f','f'),
  ('wm','fkey_data','kyf_tab','wm','fkey_data','kyf_tab','f','f'),
  ('wm','role_members','role','wm','role_members','role','f','t'),
  ('wm','role_members','member','wm','role_members','member','f','t'),
  ('wm','view_column_usage','table_schema','information_schema','view_column_usage','table_schema','f','f'),
  ('wm','view_column_usage','column_name','information_schema','view_column_usage','column_name','f','f'),
  ('wm','view_column_usage','table_catalog','information_schema','view_column_usage','table_catalog','f','f'),
  ('wm','view_column_usage','view_schema','information_schema','view_column_usage','view_schema','f','t'),
  ('wm','view_column_usage','view_catalog','information_schema','view_column_usage','view_catalog','f','f'),
  ('wm','view_column_usage','table_name','information_schema','view_column_usage','table_name','f','f'),
  ('wm','view_column_usage','view_name','information_schema','view_column_usage','view_name','f','t'),
  ('wm','fkeys_data','kst_tab','wm','fkeys_data','kst_tab','f','f'),
  ('wm','fkeys_data','ksf_cols','wm','fkeys_data','ksf_cols','f','f'),
  ('wm','fkeys_data','kst_sch','wm','fkeys_data','kst_sch','f','f'),
  ('wm','fkeys_data','kst_cols','wm','fkeys_data','kst_cols','f','f'),
  ('wm','fkeys_data','conname','wm','fkeys_data','conname','f','t'),
  ('wm','fkeys_data','ksf_tab','wm','fkeys_data','ksf_tab','f','f'),
  ('wm','fkeys_data','ksf_sch','wm','fkeys_data','ksf_sch','f','f'),
  ('wm','column_ambig','spec','wm','column_ambig','spec','f','f'),
  ('wm','column_ambig','tab','wm','column_ambig','tab','f','t'),
  ('wm','column_ambig','col','wm','column_ambig','col','f','t'),
  ('wm','column_ambig','count','wm','column_ambig','count','f','f'),
  ('wm','column_ambig','natives','wm','column_ambig','natives','f','f'),
  ('wm','column_ambig','sch','wm','column_ambig','sch','f','t'),
  ('wm','column_data','cdt_sch','wm','column_data','cdt_sch','f','t'),
  ('wm','column_data','field','wm','column_data','field','f','f'),
  ('wm','column_data','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_data','tab_kind','wm','column_data','tab_kind','f','f'),
  ('wm','column_data','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_data','is_pkey','wm','column_data','is_pkey','f','f'),
  ('wm','column_data','nonull','wm','column_data','nonull','f','f'),
  ('wm','column_data','cdt_col','wm','column_data','cdt_col','f','t'),
  ('wm','column_data','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_data','type','wm','column_data','type','f','f'),
  ('wm','column_data','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_data','length','wm','column_data','length','f','f'),
  ('wm','column_data','cdt_tab','wm','column_data','cdt_tab','f','t'),
  ('wm','column_data','def','wm','column_data','def','f','f'),
  ('wm','column_istyle','sw_value','wm','column_style','sw_value','f','f'),
  ('wm','column_istyle','cs_obj','wm','column_istyle','cs_obj','f','f'),
  ('wm','column_istyle','cs_value','wm','column_istyle','cs_value','f','f'),
  ('wm','column_istyle','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_istyle','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_istyle','nat_value','wm','column_istyle','nat_value','f','f'),
  ('wm','column_istyle','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_istyle','cs_col','wm','column_style','cs_col','f','t'),
  ('wm','column_istyle','sw_name','wm','column_style','sw_name','f','t'),
  ('wm','column_istyle','cs_sch','wm','column_style','cs_sch','f','t'),
  ('wm','column_istyle','cs_tab','wm','column_style','cs_tab','f','t'),
  ('wm','fkey_pub','key','wm','fkey_data','key','f','f'),
  ('wm','fkey_pub','ft_obj','wm','fkey_pub','ft_obj','f','f'),
  ('wm','fkey_pub','fn_tab','wm','fkey_pub','fn_tab','f','f'),
  ('wm','fkey_pub','keys','wm','fkey_data','keys','f','f'),
  ('wm','fkey_pub','fn_sch','wm','fkey_pub','fn_sch','f','f'),
  ('wm','fkey_pub','ft_tab','wm','fkey_pub','ft_tab','f','f'),
  ('wm','fkey_pub','conname','wm','fkey_data','conname','f','t'),
  ('wm','fkey_pub','fn_col','wm','fkey_pub','fn_col','f','f'),
  ('wm','fkey_pub','tt_col','wm','fkey_pub','tt_col','f','f'),
  ('wm','fkey_pub','tt_obj','wm','fkey_pub','tt_obj','f','f'),
  ('wm','fkey_pub','unikey','wm','fkey_pub','unikey','f','f'),
  ('wm','fkey_pub','ft_col','wm','fkey_pub','ft_col','f','f'),
  ('wm','fkey_pub','tn_obj','wm','fkey_pub','tn_obj','f','f'),
  ('wm','fkey_pub','tn_tab','wm','fkey_pub','tn_tab','f','f'),
  ('wm','fkey_pub','tn_col','wm','fkey_pub','tn_col','f','f'),
  ('wm','fkey_pub','fn_obj','wm','fkey_pub','fn_obj','f','f'),
  ('wm','fkey_pub','tt_sch','wm','fkey_pub','tt_sch','f','f'),
  ('wm','fkey_pub','ft_sch','wm','fkey_pub','ft_sch','f','f'),
  ('wm','fkey_pub','tt_tab','wm','fkey_pub','tt_tab','f','f'),
  ('wm','fkey_pub','tn_sch','wm','fkey_pub','tn_sch','f','f'),
  ('wm','column_pub','nat','wm','column_pub','nat','f','f'),
  ('wm','column_pub','help','wm','column_text','help','f','f'),
  ('wm','column_pub','tab','wm','column_pub','tab','f','t'),
  ('wm','column_pub','field','wm','column_data','field','f','f'),
  ('wm','column_pub','obj','wm','column_pub','obj','f','f'),
  ('wm','column_pub','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_pub','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_pub','is_pkey','wm','column_data','is_pkey','f','f'),
  ('wm','column_pub','col','wm','column_pub','col','f','t'),
  ('wm','column_pub','title','wm','column_text','title','f','f'),
  ('wm','column_pub','pkey','wm','column_native','pkey','f','f'),
  ('wm','column_pub','nonull','wm','column_data','nonull','f','f'),
  ('wm','column_pub','type','wm','column_data','type','f','f'),
  ('wm','column_pub','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_pub','length','wm','column_data','length','f','f'),
  ('wm','column_pub','def','wm','column_data','def','f','f'),
  ('wm','column_pub','sch','wm','column_pub','sch','f','t'),
  ('wm','column_pub','language','wm','column_text','language','f','f'),
  ('wm','fkeys_pub','ft_obj','wm','fkeys_pub','ft_obj','f','f'),
  ('wm','fkeys_pub','fn_tab','wm','fkeys_pub','fn_tab','f','f'),
  ('wm','fkeys_pub','fn_sch','wm','fkeys_pub','fn_sch','f','f'),
  ('wm','fkeys_pub','ft_tab','wm','fkeys_pub','ft_tab','f','f'),
  ('wm','fkeys_pub','conname','wm','fkeys_data','conname','f','t'),
  ('wm','fkeys_pub','ft_cols','wm','fkeys_pub','ft_cols','f','f'),
  ('wm','fkeys_pub','tt_obj','wm','fkeys_pub','tt_obj','f','f'),
  ('wm','fkeys_pub','tn_obj','wm','fkeys_pub','tn_obj','f','f'),
  ('wm','fkeys_pub','tn_tab','wm','fkeys_pub','tn_tab','f','f'),
  ('wm','fkeys_pub','fn_obj','wm','fkeys_pub','fn_obj','f','f'),
  ('wm','fkeys_pub','tt_cols','wm','fkeys_pub','tt_cols','f','f'),
  ('wm','fkeys_pub','tt_sch','wm','fkeys_pub','tt_sch','f','f'),
  ('wm','fkeys_pub','ft_sch','wm','fkeys_pub','ft_sch','f','f'),
  ('wm','fkeys_pub','tt_tab','wm','fkeys_pub','tt_tab','f','f'),
  ('wm','fkeys_pub','tn_sch','wm','fkeys_pub','tn_sch','f','f'),
  ('wm','table_data','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_data','obj','wm','table_data','obj','f','f'),
  ('wm','table_data','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_data','td_sch','wm','table_data','td_sch','f','t'),
  ('wm','table_data','system','wm','table_data','system','f','f'),
  ('wm','table_data','pkey','wm','column_native','pkey','f','f'),
  ('wm','table_data','td_tab','wm','table_data','td_tab','f','t'),
  ('wm','table_data','cols','wm','table_data','cols','f','f'),
  ('wm','table_lang','tab','wm','column_lang','tab','f','t'),
  ('wm','table_lang','obj','wm','table_lang','obj','f','f'),
  ('wm','table_lang','messages','wm','table_lang','messages','f','f'),
  ('wm','table_lang','columns','wm','table_lang','columns','f','f'),
  ('wm','table_lang','sch','wm','column_lang','sch','f','t'),
  ('wm','table_lang','title','wm','table_text','title','t','f'),
  ('wm','table_lang','help','wm','table_text','help','t','f'),
  ('wm','table_lang','language','wm','table_text','language','t','t'),
  ('wm','column_def','obj','wm','column_pub','obj','f','f'),
  ('wm','column_def','col','wm','column_pub','col','f','t'),
  ('wm','column_def','val','wm','column_def','val','f','f'),
  ('wm','table_pub','help','wm','table_text','help','f','f'),
  ('wm','table_pub','tab','wm','table_pub','tab','f','t'),
  ('wm','table_pub','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_pub','obj','wm','table_pub','obj','f','f'),
  ('wm','table_pub','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_pub','system','wm','table_data','system','f','f'),
  ('wm','table_pub','title','wm','table_text','title','f','f'),
  ('wm','table_pub','pkey','wm','column_native','pkey','f','f'),
  ('wm','table_pub','cols','wm','table_data','cols','f','f'),
  ('wm','table_pub','sch','wm','table_pub','sch','f','t'),
  ('wm','table_pub','language','wm','table_text','language','f','t'),
  ('json','contract','title','mychips','contracts','title','f','t'),
  ('json','contract','published','mychips','contracts','published','f','f'),
  ('json','contract','tag','mychips','contracts','tag','f','f'),
  ('json','contract','digest','mychips','contracts','digest','f','f'),
  ('json','contract','sections','mychips','contracts','sections','f','f'),
  ('json','contract','text','mychips','contracts','text','f','f'),
  ('json','contract','language','mychips','contracts','language','f','t'),
  ('json','contract','name','mychips','contracts','name','f','f'),
  ('json','contract','domain','mychips','contracts','domain','f','f'),
  ('json','contract','version','mychips','contracts','version','f','t'),
  ('json','user','middle','json','user','middle','f','f'),
  ('json','user','first','json','user','first','f','f'),
  ('json','user','begin','json','user','begin','f','f'),
  ('json','user','prefer','json','user','prefer','f','f'),
  ('json','user','cdi','json','user','cdi','f','f'),
  ('json','user','taxid','json','user','taxid','f','f'),
  ('json','user','juris','json','user','juris','f','f'),
  ('json','user','type','json','user','type','f','f'),
  ('json','user','name','json','user','name','f','f'),
  ('json','user','id','base','ent','id','f','t'),
  ('json','tally','created','json','tally','created','f','f'),
  ('json','tally','version','mychips','tallies','version','f','f'),
  ('json','tally','contract','mychips','tallies','contract','f','f'),
  ('json','tally','foil','json','tally','foil','f','f'),
  ('json','tally','id','json','tally','id','f','t'),
  ('json','tally','guid','json','tally','guid','f','f'),
  ('json','tally','stock','json','tally','stock','f','f'),
  ('mychips','tickets_v','exp_date','mychips','tokens','exp_date','f','f'),
  ('mychips','tickets_v','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','tickets_v','token','mychips','tokens','token','f','f'),
  ('mychips','tickets_v','json','mychips','tickets_v','json','f','f'),
  ('mychips','tickets_v','url','mychips','tickets_v','url','f','f'),
  ('mychips','tickets_v','id','base','ent','id','f','t'),
  ('mychips','tickets_v','token_seq','mychips','tokens','token_seq','f','t'),
  ('json','address','spec','json','address','spec','f','f'),
  ('json','address','locale','json','address','locale','f','f'),
  ('json','address','state','base','addr','state','f','f'),
  ('json','address','prior','json','address','prior','f','f'),
  ('json','address','id','json','address','id','f','t'),
  ('json','address','seq','json','address','seq','f','t'),
  ('json','address','comment','json','address','comment','f','f'),
  ('json','address','type','json','address','type','f','f'),
  ('json','address','main','json','address','main','f','f'),
  ('json','address','post','json','address','post','f','f'),
  ('json','connect','spec','json','connect','spec','f','f'),
  ('json','connect','prior','json','connect','prior','f','f'),
  ('json','connect','media','json','connect','media','f','f'),
  ('json','connect','id','json','connect','id','f','t'),
  ('json','connect','seq','json','connect','seq','f','t'),
  ('json','connect','comment','json','connect','comment','f','f'),
  ('json','users','addresses','json','users','addresses','f','f'),
  ('json','users','middle','json','user','middle','f','f'),
  ('json','users','first','json','user','first','f','f'),
  ('json','users','begin','json','user','begin','f','f'),
  ('json','users','prefer','json','user','prefer','f','f'),
  ('json','users','connects','json','users','connects','f','f'),
  ('json','users','cdi','json','user','cdi','f','f'),
  ('json','users','taxid','json','user','taxid','f','f'),
  ('json','users','juris','json','user','juris','f','f'),
  ('json','users','type','json','user','type','f','f'),
  ('json','users','name','json','user','name','f','f'),
  ('json','ticket','expires','json','ticket','expires','f','f'),
  ('json','ticket','token','mychips','tokens','token','f','f'),
  ('json','ticket','seq','json','ticket','seq','f','t'),
  ('json','ticket','public','json','ticket','public','f','f'),
  ('json','ticket','url','mychips','tickets_v','url','f','f'),
  ('json','ticket','id','base','ent','id','f','t'),
  ('mychips','paths_v','min','mychips','paths_v','min','f','f'),
  ('mychips','paths_v','cost','mychips','paths_v','cost','f','f'),
  ('mychips','paths_v','cycle','mychips','paths_v','cycle','f','f'),
  ('mychips','paths_v','uuids','mychips','paths_v','uuids','f','f'),
  ('mychips','paths_v','max','mychips','paths_v','max','f','f'),
  ('mychips','paths_v','id','mychips','paths_v','id','f','t'),
  ('mychips','paths_v','path','mychips','paths_v','path','f','f'),
  ('mychips','paths_v','circuit','mychips','paths_v','circuit','f','f'),
  ('mychips','paths_v','length','mychips','paths_v','length','f','f'),
  ('mychips','paths_v','bang','mychips','paths_v','bang','f','f'),
  ('mychips','tallies_v','user_cdi','mychips','tallies_v','user_cdi','f','f'),
  ('mychips','tallies_v','user_name','mychips','tallies_v','user_name','f','f'),
  ('mychips','tallies_v','mod_date','mychips','tallies','mod_date','f','f'),
  ('mychips','tallies_v','total','mychips','tallies_v','total','f','f'),
  ('mychips','tallies_v','state','mychips','tallies_v','state','f','f'),
  ('mychips','tallies_v','units','mychips','chits','units','f','f'),
  ('mychips','tallies_v','version','mychips','tallies','version','f','f'),
  ('mychips','tallies_v','contract','mychips','tallies','contract','f','f'),
  ('mychips','tallies_v','user_sig','mychips','tallies','user_sig','f','f'),
  ('mychips','tallies_v','part_sig','mychips','tallies','part_sig','f','f'),
  ('mychips','tallies_v','user_sock','mychips','tallies_v','user_sock','f','f'),
  ('mychips','tallies_v','dr_limit','mychips','tallies','dr_limit','f','f'),
  ('mychips','tallies_v','status','mychips','tallies','status','f','f'),
  ('mychips','tallies_v','crt_date','mychips','tallies','crt_date','f','f'),
  ('mychips','tallies_v','tally_date','mychips','tallies','tally_date','f','f'),
  ('mychips','tallies_v','cr_limit','mychips','tallies','cr_limit','f','f'),
  ('mychips','tallies_v','part_name','mychips','tallies_v','part_name','f','f'),
  ('mychips','tallies_v','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tallies_v','request','mychips','tallies','request','f','f'),
  ('mychips','tallies_v','part_cdi','mychips','tallies_v','part_cdi','f','f'),
  ('mychips','tallies_v','crt_by','mychips','tallies','crt_by','f','f'),
  ('mychips','tallies_v','tally_guid','mychips','tallies','tally_guid','f','f'),
  ('mychips','tallies_v','part_sock','mychips','tallies_v','part_sock','f','f'),
  ('mychips','tallies_v','action','mychips','tallies_v','action','f','f'),
  ('mychips','tallies_v','comment','mychips','tallies','comment','f','f'),
  ('mychips','tallies_v','total_c','mychips','tallies_v','total_c','f','f'),
  ('mychips','tallies_v','chits','mychips','tallies_v','chits','f','f'),
  ('mychips','tallies_v','json','mychips','tallies_v','json','f','f'),
  ('mychips','tallies_v','partner','mychips','tallies','partner','f','f'),
  ('mychips','tallies_v','units_c','mychips','tallies','units_c','f','f'),
  ('mychips','tallies_v','mod_by','mychips','tallies','mod_by','f','f'),
  ('mychips','tallies_v','tally_seq','mychips','tallies','tally_seq','f','f'),
  ('mychips','tallies_v','tally_ent','mychips','tallies','tally_ent','f','f'),
  ('mychips','tallies_v_sum','partners','mychips','tallies_v_sum','partners','f','f'),
  ('mychips','tallies_v_sum','total','mychips','tallies_v','total','f','f'),
  ('mychips','tallies_v_sum','vendors','mychips','tallies_v_sum','vendors','f','f'),
  ('mychips','tallies_v_sum','tallies','mychips','tallies_v_sum','tallies','f','f'),
  ('mychips','tallies_v_sum','clients','mychips','tallies_v_sum','clients','f','f'),
  ('mychips','tallies_v_sum','foils','mychips','tallies_v_sum','foils','f','f'),
  ('mychips','tallies_v_sum','stock_total_c','mychips','tallies_v_sum','stock_total_c','f','f'),
  ('mychips','tallies_v_sum','foil_total_c','mychips','tallies_v_sum','foil_total_c','f','f'),
  ('mychips','tallies_v_sum','foil_total','mychips','tallies_v_sum','foil_total','f','f'),
  ('mychips','tallies_v_sum','total_c','mychips','tallies_v','total_c','f','f'),
  ('mychips','tallies_v_sum','stock_total','mychips','tallies_v_sum','stock_total','f','f'),
  ('mychips','tallies_v_sum','stocks','mychips','tallies_v_sum','stocks','f','f'),
  ('mychips','tallies_v_sum','tally_ent','mychips','tallies','tally_ent','f','f'),
  ('mychips','chits_v','user_cdi','mychips','tallies_v','user_cdi','f','f'),
  ('mychips','chits_v','effect','mychips','chits_v','effect','f','f'),
  ('mychips','chits_v','chit_type','mychips','chits','chit_type','f','f'),
  ('mychips','chits_v','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','chits_v','state','mychips','chits_v','state','f','f'),
  ('mychips','chits_v','units','mychips','chits','units','f','f'),
  ('mychips','chits_v','value','mychips','chits_v','value','f','f'),
  ('mychips','chits_v','crt_date','mychips','chits','crt_date','f','f'),
  ('mychips','chits_v','chit_guid','mychips','chits','chit_guid','f','f'),
  ('mychips','chits_v','signature','mychips','chits','signature','f','f'),
  ('mychips','chits_v','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','chits_v','request','mychips','chits','request','f','f'),
  ('mychips','chits_v','part_cdi','mychips','tallies_v','part_cdi','f','f'),
  ('mychips','chits_v','crt_by','mychips','chits','crt_by','f','f'),
  ('mychips','chits_v','pro_quo','mychips','chits','pro_quo','f','f'),
  ('mychips','chits_v','action','mychips','chits_v','action','f','f'),
  ('mychips','chits_v','memo','mychips','chits','memo','f','f'),
  ('mychips','chits_v','json','mychips','chits_v','json','f','f'),
  ('mychips','chits_v','amount','mychips','chits_v','amount','f','f'),
  ('mychips','chits_v','chit_date','mychips','chits','chit_date','f','f'),
  ('mychips','chits_v','mod_by','mychips','chits','mod_by','f','f'),
  ('mychips','chits_v','chit_idx','mychips','chits','chit_idx','f','f'),
  ('mychips','chits_v','chit_seq','mychips','chits','chit_seq','f','f'),
  ('mychips','chits_v','chit_ent','mychips','chits','chit_ent','f','f'),
  ('mychips','users_v','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','users_v','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users_v','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v','peer_sock','mychips','users_v','peer_sock','f','f'),
  ('mychips','users_v','marital','base','ent','marital','f','f'),
  ('mychips','users_v','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','users_v','conn_pub','base','ent','conn_pub','f','f'),
  ('mychips','users_v','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','users_v','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','users_v','country','base','ent','country','f','f'),
  ('mychips','users_v','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v','age','base','ent_v','age','f','f'),
  ('mychips','users_v','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','users_v','user_inet','mychips','users','user_inet','f','f'),
  ('mychips','users_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v','user_sock','mychips','users_v','user_sock','f','f'),
  ('mychips','users_v','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','users_v','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users_v','proxy','base','ent','proxy','f','f'),
  ('mychips','users_v','title','base','ent','title','f','f'),
  ('mychips','users_v','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','users_v','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v','bank','base','ent','bank','f','f'),
  ('mychips','users_v','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users_v','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v','ent_num','base','ent','ent_num','f','f'),
  ('mychips','users_v','gender','base','ent','gender','f','f'),
  ('mychips','users_v','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v','host_id','mychips','users','host_id','f','f'),
  ('mychips','users_v','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v','username','base','ent','username','f','f'),
  ('mychips','users_v','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v','id','base','ent','id','f','t'),
  ('mychips','users_v','user_ent','mychips','users','user_ent','f','f'),
  ('mychips','users_v','peer_ent','mychips','peers','peer_ent','f','f');

--Initialization SQL:
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AF','Afghanistan','Kabul','AFN','Afghani','+93','AFG','.af');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AL','Albania','Tirana','ALL','Lek','+355','ALB','.al');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('DZ','Algeria','Algiers','DZD','Dinar','+213','DZA','.dz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AD','Andorra','Andorra la Vella','EUR','Euro','+376','AND','.ad');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AO','Angola','Luanda','AOA','Kwanza','+244','AGO','.ao');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AG','Antigua and Barbuda','Saint John''s','XCD','Dollar','+1-268','ATG','.ag');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AR','Argentina','Buenos Aires','ARS','Peso','+54','ARG','.ar');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AM','Armenia','Yerevan','AMD','Dram','+374','ARM','.am');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AU','Australia','Canberra','AUD','Dollar','+61','AUS','.au');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AT','Austria','Vienna','EUR','Euro','+43','AUT','.at');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AZ','Azerbaijan','Baku','AZN','Manat','+994','AZE','.az');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BS','Bahamas, The','Nassau','BSD','Dollar','+1-242','BHS','.bs');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BH','Bahrain','Manama','BHD','Dinar','+973','BHR','.bh');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BD','Bangladesh','Dhaka','BDT','Taka','+880','BGD','.bd');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BB','Barbados','Bridgetown','BBD','Dollar','+1-246','BRB','.bb');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BY','Belarus','Minsk','BYR','Ruble','+375','BLR','.by');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BE','Belgium','Brussels','EUR','Euro','+32','BEL','.be');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BZ','Belize','Belmopan','BZD','Dollar','+501','BLZ','.bz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BJ','Benin','Porto-Novo','XOF','Franc','+229','BEN','.bj');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BT','Bhutan','Thimphu','BTN','Ngultrum','+975','BTN','.bt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BO','Bolivia','La Paz (administrative/legislative) and Sucre (judical)','BOB','Boliviano','+591','BOL','.bo');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BA','Bosnia and Herzegovina','Sarajevo','BAM','Marka','+387','BIH','.ba');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BW','Botswana','Gaborone','BWP','Pula','+267','BWA','.bw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BR','Brazil','Brasilia','BRL','Real','+55','BRA','.br');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BN','Brunei','Bandar Seri Begawan','BND','Dollar','+673','BRN','.bn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BG','Bulgaria','Sofia','BGN','Lev','+359','BGR','.bg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BF','Burkina Faso','Ouagadougou','XOF','Franc','+226','BFA','.bf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BI','Burundi','Bujumbura','BIF','Franc','+257','BDI','.bi');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KH','Cambodia','Phnom Penh','KHR','Riels','+855','KHM','.kh');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CM','Cameroon','Yaounde','XAF','Franc','+237','CMR','.cm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CA','Canada','Ottawa','CAD','Dollar','+1','CAN','.ca');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CV','Cape Verde','Praia','CVE','Escudo','+238','CPV','.cv');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CF','Central African Republic','Bangui','XAF','Franc','+236','CAF','.cf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TD','Chad','N''Djamena','XAF','Franc','+235','TCD','.td');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CL','Chile','Santiago (administrative/judical) and Valparaiso (legislative)','CLP','Peso','+56','CHL','.cl');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CN','China, People''s Republic of','Beijing','CNY','Yuan Renminbi','+86','CHN','.cn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CO','Colombia','Bogota','COP','Peso','+57','COL','.co');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KM','Comoros','Moroni','KMF','Franc','+269','COM','.km');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CD','Congo, Democratic Republic of the (Congo � Kinshasa)','Kinshasa','CDF','Franc','+243','COD','.cd');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CG','Congo, Republic of the (Congo � Brazzaville)','Brazzaville','XAF','Franc','+242','COG','.cg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CR','Costa Rica','San Jose','CRC','Colon','+506','CRI','.cr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CI','Cote d''Ivoire (Ivory Coast)','Yamoussoukro','XOF','Franc','+225','CIV','.ci');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('HR','Croatia','Zagreb','HRK','Kuna','+385','HRV','.hr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CU','Cuba','Havana','CUP','Peso','+53','CUB','.cu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CY','Cyprus','Nicosia','CYP','Pound','+357','CYP','.cy');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CZ','Czech Republic','Prague','CZK','Koruna','+420','CZE','.cz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('DK','Denmark','Copenhagen','DKK','Krone','+45','DNK','.dk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('DJ','Djibouti','Djibouti','DJF','Franc','+253','DJI','.dj');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('DM','Dominica','Roseau','XCD','Dollar','+1-767','DMA','.dm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('DO','Dominican Republic','Santo Domingo','DOP','Peso','+1-809','DOM','.do');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('EC','Ecuador','Quito','USD','Dollar','+593','ECU','.ec');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('EG','Egypt','Cairo','EGP','Pound','+20','EGY','.eg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SV','El Salvador','San Salvador','USD','Dollar','+503','SLV','.sv');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GQ','Equatorial Guinea','Malabo','XAF','Franc','+240','GNQ','.gq');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ER','Eritrea','Asmara','ERN','Nakfa','+291','ERI','.er');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('EE','Estonia','Tallinn','EEK','Kroon','+372','EST','.ee');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ET','Ethiopia','Addis Ababa','ETB','Birr','+251','ETH','.et');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('FJ','Fiji','Suva','FJD','Dollar','+679','FJI','.fj');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('FI','Finland','Helsinki','EUR','Euro','+358','FIN','.fi');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('FR','France','Paris','EUR','Euro','+33','FRA','.fr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GA','Gabon','Libreville','XAF','Franc','+241','GAB','.ga');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GM','Gambia, The','Banjul','GMD','Dalasi','+220','GMB','.gm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GE','Georgia','Tbilisi','GEL','Lari','+995','GEO','.ge');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('DE','Germany','Berlin','EUR','Euro','+49','DEU','.de');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GH','Ghana','Accra','GHS','Cedi','+233','GHA','.gh');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GR','Greece','Athens','EUR','Euro','+30','GRC','.gr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GD','Grenada','Saint George''s','XCD','Dollar','+1-473','GRD','.gd');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GT','Guatemala','Guatemala','GTQ','Quetzal','+502','GTM','.gt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GN','Guinea','Conakry','GNF','Franc','+224','GIN','.gn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GW','Guinea-Bissau','Bissau','XOF','Franc','+245','GNB','.gw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GY','Guyana','Georgetown','GYD','Dollar','+592','GUY','.gy');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('HT','Haiti','Port-au-Prince','HTG','Gourde','+509','HTI','.ht');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('HN','Honduras','Tegucigalpa','HNL','Lempira','+504','HND','.hn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('HU','Hungary','Budapest','HUF','Forint','+36','HUN','.hu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IS','Iceland','Reykjavik','ISK','Krona','+354','ISL','.is');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IN','India','New Delhi','INR','Rupee','+91','IND','.in');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ID','Indonesia','Jakarta','IDR','Rupiah','+62','IDN','.id');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IR','Iran','Tehran','IRR','Rial','+98','IRN','.ir');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IQ','Iraq','Baghdad','IQD','Dinar','+964','IRQ','.iq');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IE','Ireland','Dublin','EUR','Euro','+353','IRL','.ie');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IL','Israel','Jerusalem','ILS','Shekel','+972','ISR','.il');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IT','Italy','Rome','EUR','Euro','+39','ITA','.it');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('JM','Jamaica','Kingston','JMD','Dollar','+1-876','JAM','.jm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('JP','Japan','Tokyo','JPY','Yen','+81','JPN','.jp');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('JO','Jordan','Amman','JOD','Dinar','+962','JOR','.jo');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KZ','Kazakhstan','Astana','KZT','Tenge','+7','KAZ','.kz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KE','Kenya','Nairobi','KES','Shilling','+254','KEN','.ke');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KI','Kiribati','Tarawa','AUD','Dollar','+686','KIR','.ki');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KP','Korea, Democratic People''s Republic of (North Korea)','Pyongyang','KPW','Won','+850','PRK','.kp');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KR','Korea, Republic of  (South Korea)','Seoul','KRW','Won','+82','KOR','.kr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KW','Kuwait','Kuwait','KWD','Dinar','+965','KWT','.kw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KG','Kyrgyzstan','Bishkek','KGS','Som','+996','KGZ','.kg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LA','Laos','Vientiane','LAK','Kip','+856','LAO','.la');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LV','Latvia','Riga','LVL','Lat','+371','LVA','.lv');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LB','Lebanon','Beirut','LBP','Pound','+961','LBN','.lb');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LS','Lesotho','Maseru','LSL','Loti','+266','LSO','.ls');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LR','Liberia','Monrovia','LRD','Dollar','+231','LBR','.lr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LY','Libya','Tripoli','LYD','Dinar','+218','LBY','.ly');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LI','Liechtenstein','Vaduz','CHF','Franc','+423','LIE','.li');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LT','Lithuania','Vilnius','LTL','Litas','+370','LTU','.lt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LU','Luxembourg','Luxembourg','EUR','Euro','+352','LUX','.lu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MK','Macedonia','Skopje','MKD','Denar','+389','MKD','.mk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MG','Madagascar','Antananarivo','MGA','Ariary','+261','MDG','.mg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MW','Malawi','Lilongwe','MWK','Kwacha','+265','MWI','.mw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MY','Malaysia','Kuala Lumpur (legislative/judical) and Putrajaya (administrative)','MYR','Ringgit','+60','MYS','.my');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MV','Maldives','Male','MVR','Rufiyaa','+960','MDV','.mv');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ML','Mali','Bamako','XOF','Franc','+223','MLI','.ml');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MT','Malta','Valletta','MTL','Lira','+356','MLT','.mt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MH','Marshall Islands','Majuro','USD','Dollar','+692','MHL','.mh');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MR','Mauritania','Nouakchott','MRO','Ouguiya','+222','MRT','.mr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MU','Mauritius','Port Louis','MUR','Rupee','+230','MUS','.mu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MX','Mexico','Mexico','MXN','Peso','+52','MEX','.mx');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('FM','Micronesia','Palikir','USD','Dollar','+691','FSM','.fm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MD','Moldova','Chisinau','MDL','Leu','+373','MDA','.md');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MC','Monaco','Monaco','EUR','Euro','+377','MCO','.mc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MN','Mongolia','Ulaanbaatar','MNT','Tugrik','+976','MNG','.mn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MA','Morocco','Rabat','MAD','Dirham','+212','MAR','.ma');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MZ','Mozambique','Maputo','MZM','Meticail','+258','MOZ','.mz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MM','Myanmar (Burma)','Naypyidaw','MMK','Kyat','+95','MMR','.mm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NA','Namibia','Windhoek','NAD','Dollar','+264','NAM','.na');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NR','Nauru','Yaren','AUD','Dollar','+674','NRU','.nr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NP','Nepal','Kathmandu','NPR','Rupee','+977','NPL','.np');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NL','Netherlands','Amsterdam (administrative) and The Hague (legislative/judical)','EUR','Euro','+31','NLD','.nl');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NZ','New Zealand','Wellington','NZD','Dollar','+64','NZL','.nz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NI','Nicaragua','Managua','NIO','Cordoba','+505','NIC','.ni');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NE','Niger','Niamey','XOF','Franc','+227','NER','.ne');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NG','Nigeria','Abuja','NGN','Naira','+234','NGA','.ng');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NO','Norway','Oslo','NOK','Krone','+47','NOR','.no');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('OM','Oman','Muscat','OMR','Rial','+968','OMN','.om');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PK','Pakistan','Islamabad','PKR','Rupee','+92','PAK','.pk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PW','Palau','Melekeok','USD','Dollar','+680','PLW','.pw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PA','Panama','Panama','PAB','Balboa','+507','PAN','.pa');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PG','Papua New Guinea','Port Moresby','PGK','Kina','+675','PNG','.pg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PY','Paraguay','Asuncion','PYG','Guarani','+595','PRY','.py');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PE','Peru','Lima','PEN','Sol','+51','PER','.pe');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PH','Philippines','Manila','PHP','Peso','+63','PHL','.ph');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PL','Poland','Warsaw','PLN','Zloty','+48','POL','.pl');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PT','Portugal','Lisbon','EUR','Euro','+351','PRT','.pt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('QA','Qatar','Doha','QAR','Rial','+974','QAT','.qa');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('RO','Romania','Bucharest','RON','Leu','+40','ROU','.ro');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('RW','Rwanda','Kigali','RWF','Franc','+250','RWA','.rw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KN','Saint Kitts and Nevis','Basseterre','XCD','Dollar','+1-869','KNA','.kn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LC','Saint Lucia','Castries','XCD','Dollar','+1-758','LCA','.lc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VC','Saint Vincent and the Grenadines','Kingstown','XCD','Dollar','+1-784','VCT','.vc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('WS','Samoa','Apia','WST','Tala','+685','WSM','.ws');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SM','San Marino','San Marino','EUR','Euro','+378','SMR','.sm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ST','Sao Tome and Principe','Sao Tome','STD','Dobra','+239','STP','.st');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SA','Saudi Arabia','Riyadh','SAR','Rial','+966','SAU','.sa');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SN','Senegal','Dakar','XOF','Franc','+221','SEN','.sn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SC','Seychelles','Victoria','SCR','Rupee','+248','SYC','.sc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SL','Sierra Leone','Freetown','SLL','Leone','+232','SLE','.sl');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SG','Singapore','Singapore','SGD','Dollar','+65','SGP','.sg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SK','Slovakia','Bratislava','SKK','Koruna','+421','SVK','.sk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SI','Slovenia','Ljubljana','EUR','Euro','+386','SVN','.si');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SB','Solomon Islands','Honiara','SBD','Dollar','+677','SLB','.sb');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SO','Somalia','Mogadishu','SOS','Shilling','+252','SOM','.so');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ZA','South Africa','Pretoria (administrative), Cape Town (legislative), and Bloemfontein (judical)','ZAR','Rand','+27','ZAF','.za');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ES','Spain','Madrid','EUR','Euro','+34','ESP','.es');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('LK','Sri Lanka','Colombo (administrative/judical) and Sri Jayewardenepura Kotte (legislative)','LKR','Rupee','+94','LKA','.lk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SD','Sudan','Khartoum','SDG','Pound','+249','SDN','.sd');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SR','Suriname','Paramaribo','SRD','Dollar','+597','SUR','.sr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SZ','Swaziland','Mbabane (administrative) and Lobamba (legislative)','SZL','Lilangeni','+268','SWZ','.sz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SE','Sweden','Stockholm','SEK','Kronoa','+46','SWE','.se');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CH','Switzerland','Bern','CHF','Franc','+41','CHE','.ch');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SY','Syria','Damascus','SYP','Pound','+963','SYR','.sy');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TJ','Tajikistan','Dushanbe','TJS','Somoni','+992','TJK','.tj');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TZ','Tanzania','Dar es Salaam (administrative/judical) and Dodoma (legislative)','TZS','Shilling','+255','TZA','.tz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TH','Thailand','Bangkok','THB','Baht','+66','THA','.th');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TG','Togo','Lome','XOF','Franc','+228','TGO','.tg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TO','Tonga','Nuku''alofa','TOP','Pa''anga','+676','TON','.to');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TT','Trinidad and Tobago','Port-of-Spain','TTD','Dollar','+1-868','TTO','.tt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TN','Tunisia','Tunis','TND','Dinar','+216','TUN','.tn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TR','Turkey','Ankara','TRY','Lira','+90','TUR','.tr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TM','Turkmenistan','Ashgabat','TMM','Manat','+993','TKM','.tm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TV','Tuvalu','Funafuti','AUD','Dollar','+688','TUV','.tv');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('UG','Uganda','Kampala','UGX','Shilling','+256','UGA','.ug');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('UA','Ukraine','Kiev','UAH','Hryvnia','+380','UKR','.ua');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AE','United Arab Emirates','Abu Dhabi','AED','Dirham','+971','ARE','.ae');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GB','United Kingdom','London','GBP','Pound','+44','GBR','.uk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('US','United States','Washington','USD','Dollar','+1','USA','.us');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('UY','Uruguay','Montevideo','UYU','Peso','+598','URY','.uy');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('UZ','Uzbekistan','Tashkent','UZS','Som','+998','UZB','.uz');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VU','Vanuatu','Port-Vila','VUV','Vatu','+678','VUT','.vu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VA','Vatican City','Vatican City','EUR','Euro','+379','VAT','.va');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VE','Venezuela','Caracas','VEB','Bolivar','+58','VEN','.ve');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VN','Vietnam','Hanoi','VND','Dong','+84','VNM','.vn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('YE','Yemen','Sanaa','YER','Rial','+967','YEM','.ye');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ZM','Zambia','Lusaka','ZMK','Kwacha','+260','ZMB','.zm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('ZW','Zimbabwe','Harare','ZWD','Dollar','+263','ZWE','.zw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TW','China, Republic of (Taiwan)','Taipei','TWD','Dollar','+886','TWN','.tw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CX','Christmas Island','The Settlement (Flying Fish Cove)','AUD','Dollar','+61','CXR','.cx');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CC','Cocos (Keeling) Islands','West Island','AUD','Dollar','+61','CCK','.cc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('HM','Heard Island and McDonald Islands','','','','','HMD','.hm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NF','Norfolk Island','Kingston','AUD','Dollar','+672','NFK','.nf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NC','New Caledonia','Noumea','XPF','Franc','+687','NCL','.nc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PF','French Polynesia','Papeete','XPF','Franc','+689','PYF','.pf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('YT','Mayotte','Mamoudzou','EUR','Euro','+262','MYT','.yt');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GP','Saint Barthelemy','Gustavia','EUR','Euro','+590','GLP','.gp');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PM','Saint Pierre and Miquelon','Saint-Pierre','EUR','Euro','+508','SPM','.pm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('WF','Wallis and Futuna','Mata''utu','XPF','Franc','+681','WLF','.wf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TF','French Southern and Antarctic Lands','Martin-de-Vivi�s','','','','ATF','.tf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BV','Bouvet Island','','','','','BVT','.bv');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('CK','Cook Islands','Avarua','NZD','Dollar','+682','COK','.ck');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('NU','Niue','Alofi','NZD','Dollar','+683','NIU','.nu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TK','Tokelau','','NZD','Dollar','+690','TKL','.tk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GG','Guernsey','Saint Peter Port','GGP','Pound','+44','GGY','.gg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IM','Isle of Man','Douglas','IMP','Pound','+44','IMN','.im');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('JE','Jersey','Saint Helier','JEP','Pound','+44','JEY','.je');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AI','Anguilla','The Valley','XCD','Dollar','+1-264','AIA','.ai');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('BM','Bermuda','Hamilton','BMD','Dollar','+1-441','BMU','.bm');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('IO','British Indian Ocean Territory','','','','+246','IOT','.io');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VG','British Virgin Islands','Road Town','USD','Dollar','+1-284','VGB','.vg');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('KY','Cayman Islands','George Town','KYD','Dollar','+1-345','CYM','.ky');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('FK','Falkland Islands (Islas Malvinas)','Stanley','FKP','Pound','+500','FLK','.fk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GI','Gibraltar','Gibraltar','GIP','Pound','+350','GIB','.gi');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MS','Montserrat','Plymouth','XCD','Dollar','+1-664','MSR','.ms');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PN','Pitcairn Islands','Adamstown','NZD','Dollar','','PCN','.pn');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SH','Saint Helena','Jamestown','SHP','Pound','+290','SHN','.sh');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GS','South Georgia and the South Sandwich Islands','','','','','SGS','.gs');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TC','Turks and Caicos Islands','Grand Turk','USD','Dollar','+1-649','TCA','.tc');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MP','Northern Mariana Islands','Saipan','USD','Dollar','+1-670','MNP','.mp');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PR','Puerto Rico','San Juan','USD','Dollar','+1-787','PRI','.pr');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AS','American Samoa','Pago Pago','USD','Dollar','+1-684','ASM','.as');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('UM','Baker Island','','','','','UMI','');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GU','Guam','Hagatna','USD','Dollar','+1-671','GUM','.gu');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('VI','U.S. Virgin Islands','Charlotte Amalie','USD','Dollar','+1-340','VIR','.vi');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('HK','Hong Kong','','HKD','Dollar','+852','HKG','.hk');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MO','Macau','Macau','MOP','Pataca','+853','MAC','.mo');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('FO','Faroe Islands','Torshavn','DKK','Krone','+298','FRO','.fo');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GL','Greenland','Nuuk (Godthab)','DKK','Krone','+299','GRL','.gl');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('GF','French Guiana','Cayenne','EUR','Euro','+594','GUF','.gf');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('MQ','Martinique','Fort-de-France','EUR','Euro','+596','MTQ','.mq');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('RE','Reunion','Saint-Denis','EUR','Euro','+262','REU','.re');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AX','Aland','Mariehamn','EUR','Euro','+358-18','ALA','.ax');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AW','Aruba','Oranjestad','AWG','Guilder','+297','ABW','.aw');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AN','Netherlands Antilles','Willemstad','ANG','Guilder','+599','ANT','.an');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('SJ','Svalbard','Longyearbyen','NOK','Krone','+47','SJM','.sj');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AC','Ascension','Georgetown','SHP','Pound','+247','ASC','.ac');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('TA','Tristan da Cunha','Edinburgh','SHP','Pound','+290','TAA','');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('AQ','Antarctica','','','','','ATA','.aq');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('PS','Palestinian Territories (Gaza Strip and West Bank)','Gaza City (Gaza Strip) and Ramallah (West Bank)','ILS','Shekel','+970','PSE','.ps');
insert into base.country (code,com_name,capital,cur_code,cur_name,dial_code,iso_3,iana) values ('EH','Western Sahara','El-Aaiun','MAD','Dirham','+212','ESH','.eh');
insert into base.ent (ent_name,ent_type,username,country) values ('Admin','r',session_user,'US');
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'aar'
    , 'aar'
    , 'aa'
    , 'Afar'
    , 'afar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'abk'
    , 'abk'
    , 'ab'
    , 'Abkhazian'
    , 'abkhaze'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ace'
    , 'ace'
    , null
    , 'Achinese'
    , 'aceh'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ach'
    , 'ach'
    , null
    , 'Acoli'
    , 'acoli'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ada'
    , 'ada'
    , null
    , 'Adangme'
    , 'adangme'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ady'
    , 'ady'
    , null
    , 'Adyghe; Adygei'
    , 'adyghé'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'afa'
    , 'afa'
    , null
    , 'Afro-Asiatic languages'
    , 'afro-asiatiques, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'afh'
    , 'afh'
    , null
    , 'Afrihili'
    , 'afrihili'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'afr'
    , 'afr'
    , 'af'
    , 'Afrikaans'
    , 'afrikaans'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ain'
    , 'ain'
    , null
    , 'Ainu'
    , 'aïnou'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'aka'
    , 'aka'
    , 'ak'
    , 'Akan'
    , 'akan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'akk'
    , 'akk'
    , null
    , 'Akkadian'
    , 'akkadien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sqi'
    , 'alb'
    , 'sq'
    , 'Albanian'
    , 'albanais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ale'
    , 'ale'
    , null
    , 'Aleut'
    , 'aléoute'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'alg'
    , 'alg'
    , null
    , 'Algonquian languages'
    , 'algonquines, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'alt'
    , 'alt'
    , null
    , 'Southern Altai'
    , 'altai du Sud'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'amh'
    , 'amh'
    , 'am'
    , 'Amharic'
    , 'amharique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ang'
    , 'ang'
    , null
    , 'English, Old (ca.450-1100)'
    , 'anglo-saxon (ca.450-1100)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'anp'
    , 'anp'
    , null
    , 'Angika'
    , 'angika'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'apa'
    , 'apa'
    , null
    , 'Apache languages'
    , 'apaches, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ara'
    , 'ara'
    , 'ar'
    , 'Arabic'
    , 'arabe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'arc'
    , 'arc'
    , null
    , 'Official Aramaic (700-300 BCE); Imperial Aramaic (700-300 BCE)'
    , 'araméen d''empire (700-300 BCE)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'arg'
    , 'arg'
    , 'an'
    , 'Aragonese'
    , 'aragonais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hye'
    , 'arm'
    , 'hy'
    , 'Armenian'
    , 'arménien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'arn'
    , 'arn'
    , null
    , 'Mapudungun; Mapuche'
    , 'mapudungun; mapuche; mapuce'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'arp'
    , 'arp'
    , null
    , 'Arapaho'
    , 'arapaho'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'art'
    , 'art'
    , null
    , 'Artificial languages'
    , 'artificielles, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'arw'
    , 'arw'
    , null
    , 'Arawak'
    , 'arawak'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'asm'
    , 'asm'
    , 'as'
    , 'Assamese'
    , 'assamais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ast'
    , 'ast'
    , null
    , 'Asturian; Bable; Leonese; Asturleonese'
    , 'asturien; bable; léonais; asturoléonais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ath'
    , 'ath'
    , null
    , 'Athapascan languages'
    , 'athapascanes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'aus'
    , 'aus'
    , null
    , 'Australian languages'
    , 'australiennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ava'
    , 'ava'
    , 'av'
    , 'Avaric'
    , 'avar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ave'
    , 'ave'
    , 'ae'
    , 'Avestan'
    , 'avestique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'awa'
    , 'awa'
    , null
    , 'Awadhi'
    , 'awadhi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'aym'
    , 'aym'
    , 'ay'
    , 'Aymara'
    , 'aymara'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'aze'
    , 'aze'
    , 'az'
    , 'Azerbaijani'
    , 'azéri'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bad'
    , 'bad'
    , null
    , 'Banda languages'
    , 'banda, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bai'
    , 'bai'
    , null
    , 'Bamileke languages'
    , 'bamiléké, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bak'
    , 'bak'
    , 'ba'
    , 'Bashkir'
    , 'bachkir'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bal'
    , 'bal'
    , null
    , 'Baluchi'
    , 'baloutchi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bam'
    , 'bam'
    , 'bm'
    , 'Bambara'
    , 'bambara'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ban'
    , 'ban'
    , null
    , 'Balinese'
    , 'balinais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'eus'
    , 'baq'
    , 'eu'
    , 'Basque'
    , 'basque'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bas'
    , 'bas'
    , null
    , 'Basa'
    , 'basa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bat'
    , 'bat'
    , null
    , 'Baltic languages'
    , 'baltes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bej'
    , 'bej'
    , null
    , 'Beja; Bedawiyet'
    , 'bedja'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bel'
    , 'bel'
    , 'be'
    , 'Belarusian'
    , 'biélorusse'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bem'
    , 'bem'
    , null
    , 'Bemba'
    , 'bemba'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ben'
    , 'ben'
    , 'bn'
    , 'Bengali'
    , 'bengali'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ber'
    , 'ber'
    , null
    , 'Berber languages'
    , 'berbères, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bho'
    , 'bho'
    , null
    , 'Bhojpuri'
    , 'bhojpuri'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bih'
    , 'bih'
    , 'bh'
    , 'Bihari languages'
    , 'langues biharis'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bik'
    , 'bik'
    , null
    , 'Bikol'
    , 'bikol'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bin'
    , 'bin'
    , null
    , 'Bini; Edo'
    , 'bini; edo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bis'
    , 'bis'
    , 'bi'
    , 'Bislama'
    , 'bichlamar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bla'
    , 'bla'
    , null
    , 'Siksika'
    , 'blackfoot'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bnt'
    , 'bnt'
    , null
    , 'Bantu (Other)'
    , 'bantoues, autres langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bos'
    , 'bos'
    , 'bs'
    , 'Bosnian'
    , 'bosniaque'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bra'
    , 'bra'
    , null
    , 'Braj'
    , 'braj'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bre'
    , 'bre'
    , 'br'
    , 'Breton'
    , 'breton'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'btk'
    , 'btk'
    , null
    , 'Batak languages'
    , 'batak, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bua'
    , 'bua'
    , null
    , 'Buriat'
    , 'bouriate'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bug'
    , 'bug'
    , null
    , 'Buginese'
    , 'bugi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bul'
    , 'bul'
    , 'bg'
    , 'Bulgarian'
    , 'bulgare'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mya'
    , 'bur'
    , 'my'
    , 'Burmese'
    , 'birman'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'byn'
    , 'byn'
    , null
    , 'Blin; Bilin'
    , 'blin; bilen'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cad'
    , 'cad'
    , null
    , 'Caddo'
    , 'caddo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cai'
    , 'cai'
    , null
    , 'Central American Indian languages'
    , 'amérindiennes de L''Amérique centrale, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'car'
    , 'car'
    , null
    , 'Galibi Carib'
    , 'karib; galibi; carib'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cat'
    , 'cat'
    , 'ca'
    , 'Catalan; Valencian'
    , 'catalan; valencien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cau'
    , 'cau'
    , null
    , 'Caucasian languages'
    , 'caucasiennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ceb'
    , 'ceb'
    , null
    , 'Cebuano'
    , 'cebuano'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cel'
    , 'cel'
    , null
    , 'Celtic languages'
    , 'celtiques, langues; celtes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cha'
    , 'cha'
    , 'ch'
    , 'Chamorro'
    , 'chamorro'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chb'
    , 'chb'
    , null
    , 'Chibcha'
    , 'chibcha'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'che'
    , 'che'
    , 'ce'
    , 'Chechen'
    , 'tchétchène'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chg'
    , 'chg'
    , null
    , 'Chagatai'
    , 'djaghataï'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zho'
    , 'chi'
    , 'zh'
    , 'Chinese'
    , 'chinois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chk'
    , 'chk'
    , null
    , 'Chuukese'
    , 'chuuk'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chm'
    , 'chm'
    , null
    , 'Mari'
    , 'mari'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chn'
    , 'chn'
    , null
    , 'Chinook jargon'
    , 'chinook, jargon'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cho'
    , 'cho'
    , null
    , 'Choctaw'
    , 'choctaw'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chp'
    , 'chp'
    , null
    , 'Chipewyan; Dene Suline'
    , 'chipewyan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chr'
    , 'chr'
    , null
    , 'Cherokee'
    , 'cherokee'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chu'
    , 'chu'
    , 'cu'
    , 'Church Slavic; Old Slavonic; Church Slavonic; Old Bulgarian; Old Church Slavonic'
    , 'slavon d''église; vieux slave; slavon liturgique; vieux bulgare'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chv'
    , 'chv'
    , 'cv'
    , 'Chuvash'
    , 'tchouvache'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'chy'
    , 'chy'
    , null
    , 'Cheyenne'
    , 'cheyenne'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cmc'
    , 'cmc'
    , null
    , 'Chamic languages'
    , 'chames, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cnr'
    , 'cnr'
    , null
    , 'Montenegrin'
    , 'monténégrin'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cop'
    , 'cop'
    , null
    , 'Coptic'
    , 'copte'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cor'
    , 'cor'
    , 'kw'
    , 'Cornish'
    , 'cornique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cos'
    , 'cos'
    , 'co'
    , 'Corsican'
    , 'corse'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cpe'
    , 'cpe'
    , null
    , 'Creoles and pidgins, English based'
    , 'créoles et pidgins basés sur l''anglais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cpf'
    , 'cpf'
    , null
    , 'Creoles and pidgins, French-based'
    , 'créoles et pidgins basés sur le français'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cpp'
    , 'cpp'
    , null
    , 'Creoles and pidgins, Portuguese-based'
    , 'créoles et pidgins basés sur le portugais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cre'
    , 'cre'
    , 'cr'
    , 'Cree'
    , 'cree'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'crh'
    , 'crh'
    , null
    , 'Crimean Tatar; Crimean Turkish'
    , 'tatar de Crimé'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'crp'
    , 'crp'
    , null
    , 'Creoles and pidgins'
    , 'créoles et pidgins'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'csb'
    , 'csb'
    , null
    , 'Kashubian'
    , 'kachoube'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cus'
    , 'cus'
    , null
    , 'Cushitic languages'
    , 'couchitiques, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ces'
    , 'cze'
    , 'cs'
    , 'Czech'
    , 'tchèque'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dak'
    , 'dak'
    , null
    , 'Dakota'
    , 'dakota'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dan'
    , 'dan'
    , 'da'
    , 'Danish'
    , 'danois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dar'
    , 'dar'
    , null
    , 'Dargwa'
    , 'dargwa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'day'
    , 'day'
    , null
    , 'Land Dayak languages'
    , 'dayak, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'del'
    , 'del'
    , null
    , 'Delaware'
    , 'delaware'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'den'
    , 'den'
    , null
    , 'Slave (Athapascan)'
    , 'esclave (athapascan)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dgr'
    , 'dgr'
    , null
    , 'Dogrib'
    , 'dogrib'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'din'
    , 'din'
    , null
    , 'Dinka'
    , 'dinka'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'div'
    , 'div'
    , 'dv'
    , 'Divehi; Dhivehi; Maldivian'
    , 'maldivien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'doi'
    , 'doi'
    , null
    , 'Dogri'
    , 'dogri'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dra'
    , 'dra'
    , null
    , 'Dravidian languages'
    , 'dravidiennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dsb'
    , 'dsb'
    , null
    , 'Lower Sorbian'
    , 'bas-sorabe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dua'
    , 'dua'
    , null
    , 'Duala'
    , 'douala'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dum'
    , 'dum'
    , null
    , 'Dutch, Middle (ca.1050-1350)'
    , 'néerlandais moyen (ca. 1050-1350)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nld'
    , 'dut'
    , 'nl'
    , 'Dutch; Flemish'
    , 'néerlandais; flamand'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dyu'
    , 'dyu'
    , null
    , 'Dyula'
    , 'dioula'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'dzo'
    , 'dzo'
    , 'dz'
    , 'Dzongkha'
    , 'dzongkha'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'efi'
    , 'efi'
    , null
    , 'Efik'
    , 'efik'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'egy'
    , 'egy'
    , null
    , 'Egyptian (Ancient)'
    , 'égyptien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'eka'
    , 'eka'
    , null
    , 'Ekajuk'
    , 'ekajuk'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'elx'
    , 'elx'
    , null
    , 'Elamite'
    , 'élamite'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'eng'
    , 'eng'
    , 'en'
    , 'English'
    , 'anglais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'enm'
    , 'enm'
    , null
    , 'English, Middle (1100-1500)'
    , 'anglais moyen (1100-1500)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'epo'
    , 'epo'
    , 'eo'
    , 'Esperanto'
    , 'espéranto'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'est'
    , 'est'
    , 'et'
    , 'Estonian'
    , 'estonien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ewe'
    , 'ewe'
    , 'ee'
    , 'Ewe'
    , 'éwé'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ewo'
    , 'ewo'
    , null
    , 'Ewondo'
    , 'éwondo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fan'
    , 'fan'
    , null
    , 'Fang'
    , 'fang'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fao'
    , 'fao'
    , 'fo'
    , 'Faroese'
    , 'féroïen'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fat'
    , 'fat'
    , null
    , 'Fanti'
    , 'fanti'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fij'
    , 'fij'
    , 'fj'
    , 'Fijian'
    , 'fidjien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fil'
    , 'fil'
    , null
    , 'Filipino; Pilipino'
    , 'filipino; pilipino'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fin'
    , 'fin'
    , 'fi'
    , 'Finnish'
    , 'finnois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fiu'
    , 'fiu'
    , null
    , 'Finno-Ugrian languages'
    , 'finno-ougriennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fon'
    , 'fon'
    , null
    , 'Fon'
    , 'fon'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fra'
    , 'fre'
    , 'fr'
    , 'French'
    , 'français'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'frm'
    , 'frm'
    , null
    , 'French, Middle (ca.1400-1600)'
    , 'français moyen (1400-1600)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fro'
    , 'fro'
    , null
    , 'French, Old (842-ca.1400)'
    , 'français ancien (842-ca.1400)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'frr'
    , 'frr'
    , null
    , 'Northern Frisian'
    , 'frison septentrional'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'frs'
    , 'frs'
    , null
    , 'Eastern Frisian'
    , 'frison oriental'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fry'
    , 'fry'
    , 'fy'
    , 'Western Frisian'
    , 'frison occidental'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ful'
    , 'ful'
    , 'ff'
    , 'Fulah'
    , 'peul'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fur'
    , 'fur'
    , null
    , 'Friulian'
    , 'frioulan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gaa'
    , 'gaa'
    , null
    , 'Ga'
    , 'ga'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gay'
    , 'gay'
    , null
    , 'Gayo'
    , 'gayo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gba'
    , 'gba'
    , null
    , 'Gbaya'
    , 'gbaya'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gem'
    , 'gem'
    , null
    , 'Germanic languages'
    , 'germaniques, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kat'
    , 'geo'
    , 'ka'
    , 'Georgian'
    , 'géorgien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'deu'
    , 'ger'
    , 'de'
    , 'German'
    , 'allemand'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gez'
    , 'gez'
    , null
    , 'Geez'
    , 'guèze'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gil'
    , 'gil'
    , null
    , 'Gilbertese'
    , 'kiribati'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gla'
    , 'gla'
    , 'gd'
    , 'Gaelic; Scottish Gaelic'
    , 'gaélique; gaélique écossais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gle'
    , 'gle'
    , 'ga'
    , 'Irish'
    , 'irlandais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'glg'
    , 'glg'
    , 'gl'
    , 'Galician'
    , 'galicien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'glv'
    , 'glv'
    , 'gv'
    , 'Manx'
    , 'manx; mannois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gmh'
    , 'gmh'
    , null
    , 'German, Middle High (ca.1050-1500)'
    , 'allemand, moyen haut (ca. 1050-1500)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'goh'
    , 'goh'
    , null
    , 'German, Old High (ca.750-1050)'
    , 'allemand, vieux haut (ca. 750-1050)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gon'
    , 'gon'
    , null
    , 'Gondi'
    , 'gond'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gor'
    , 'gor'
    , null
    , 'Gorontalo'
    , 'gorontalo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'got'
    , 'got'
    , null
    , 'Gothic'
    , 'gothique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'grb'
    , 'grb'
    , null
    , 'Grebo'
    , 'grebo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'grc'
    , 'grc'
    , null
    , 'Greek, Ancient (to 1453)'
    , 'grec ancien (jusqu''à 1453)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ell'
    , 'gre'
    , 'el'
    , 'Greek, Modern (1453-)'
    , 'grec moderne (après 1453)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'grn'
    , 'grn'
    , 'gn'
    , 'Guarani'
    , 'guarani'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gsw'
    , 'gsw'
    , null
    , 'Swiss German; Alemannic; Alsatian'
    , 'suisse alémanique; alémanique; alsacien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'guj'
    , 'guj'
    , 'gu'
    , 'Gujarati'
    , 'goudjrati'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'gwi'
    , 'gwi'
    , null
    , 'Gwich''in'
    , 'gwich''in'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hai'
    , 'hai'
    , null
    , 'Haida'
    , 'haida'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hat'
    , 'hat'
    , 'ht'
    , 'Haitian; Haitian Creole'
    , 'haïtien; créole haïtien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hau'
    , 'hau'
    , 'ha'
    , 'Hausa'
    , 'haoussa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'haw'
    , 'haw'
    , null
    , 'Hawaiian'
    , 'hawaïen'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'heb'
    , 'heb'
    , 'he'
    , 'Hebrew'
    , 'hébreu'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'her'
    , 'her'
    , 'hz'
    , 'Herero'
    , 'herero'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hil'
    , 'hil'
    , null
    , 'Hiligaynon'
    , 'hiligaynon'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'him'
    , 'him'
    , null
    , 'Himachali languages; Western Pahari languages'
    , 'langues himachalis; langues paharis occidentales'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hin'
    , 'hin'
    , 'hi'
    , 'Hindi'
    , 'hindi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hit'
    , 'hit'
    , null
    , 'Hittite'
    , 'hittite'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hmn'
    , 'hmn'
    , null
    , 'Hmong; Mong'
    , 'hmong'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hmo'
    , 'hmo'
    , 'ho'
    , 'Hiri Motu'
    , 'hiri motu'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hrv'
    , 'hrv'
    , 'hr'
    , 'Croatian'
    , 'croate'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hsb'
    , 'hsb'
    , null
    , 'Upper Sorbian'
    , 'haut-sorabe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hun'
    , 'hun'
    , 'hu'
    , 'Hungarian'
    , 'hongrois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'hup'
    , 'hup'
    , null
    , 'Hupa'
    , 'hupa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'iba'
    , 'iba'
    , null
    , 'Iban'
    , 'iban'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ibo'
    , 'ibo'
    , 'ig'
    , 'Igbo'
    , 'igbo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'isl'
    , 'ice'
    , 'is'
    , 'Icelandic'
    , 'islandais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ido'
    , 'ido'
    , 'io'
    , 'Ido'
    , 'ido'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'iii'
    , 'iii'
    , 'ii'
    , 'Sichuan Yi; Nuosu'
    , 'yi de Sichuan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ijo'
    , 'ijo'
    , null
    , 'Ijo languages'
    , 'ijo, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'iku'
    , 'iku'
    , 'iu'
    , 'Inuktitut'
    , 'inuktitut'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ile'
    , 'ile'
    , 'ie'
    , 'Interlingue; Occidental'
    , 'interlingue'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ilo'
    , 'ilo'
    , null
    , 'Iloko'
    , 'ilocano'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ina'
    , 'ina'
    , 'ia'
    , 'Interlingua (International Auxiliary Language Association)'
    , 'interlingua (langue auxiliaire internationale)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'inc'
    , 'inc'
    , null
    , 'Indic languages'
    , 'indo-aryennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ind'
    , 'ind'
    , 'id'
    , 'Indonesian'
    , 'indonésien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ine'
    , 'ine'
    , null
    , 'Indo-European languages'
    , 'indo-européennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'inh'
    , 'inh'
    , null
    , 'Ingush'
    , 'ingouche'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ipk'
    , 'ipk'
    , 'ik'
    , 'Inupiaq'
    , 'inupiaq'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ira'
    , 'ira'
    , null
    , 'Iranian languages'
    , 'iraniennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'iro'
    , 'iro'
    , null
    , 'Iroquoian languages'
    , 'iroquoises, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ita'
    , 'ita'
    , 'it'
    , 'Italian'
    , 'italien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'jav'
    , 'jav'
    , 'jv'
    , 'Javanese'
    , 'javanais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'jbo'
    , 'jbo'
    , null
    , 'Lojban'
    , 'lojban'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'jpn'
    , 'jpn'
    , 'ja'
    , 'Japanese'
    , 'japonais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'jpr'
    , 'jpr'
    , null
    , 'Judeo-Persian'
    , 'judéo-persan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'jrb'
    , 'jrb'
    , null
    , 'Judeo-Arabic'
    , 'judéo-arabe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kaa'
    , 'kaa'
    , null
    , 'Kara-Kalpak'
    , 'karakalpak'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kab'
    , 'kab'
    , null
    , 'Kabyle'
    , 'kabyle'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kac'
    , 'kac'
    , null
    , 'Kachin; Jingpho'
    , 'kachin; jingpho'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kal'
    , 'kal'
    , 'kl'
    , 'Kalaallisut; Greenlandic'
    , 'groenlandais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kam'
    , 'kam'
    , null
    , 'Kamba'
    , 'kamba'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kan'
    , 'kan'
    , 'kn'
    , 'Kannada'
    , 'kannada'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kar'
    , 'kar'
    , null
    , 'Karen languages'
    , 'karen, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kas'
    , 'kas'
    , 'ks'
    , 'Kashmiri'
    , 'kashmiri'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kau'
    , 'kau'
    , 'kr'
    , 'Kanuri'
    , 'kanouri'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kaw'
    , 'kaw'
    , null
    , 'Kawi'
    , 'kawi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kaz'
    , 'kaz'
    , 'kk'
    , 'Kazakh'
    , 'kazakh'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kbd'
    , 'kbd'
    , null
    , 'Kabardian'
    , 'kabardien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kha'
    , 'kha'
    , null
    , 'Khasi'
    , 'khasi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'khi'
    , 'khi'
    , null
    , 'Khoisan languages'
    , 'khoïsan, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'khm'
    , 'khm'
    , 'km'
    , 'Central Khmer'
    , 'khmer central'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kho'
    , 'kho'
    , null
    , 'Khotanese; Sakan'
    , 'khotanais; sakan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kik'
    , 'kik'
    , 'ki'
    , 'Kikuyu; Gikuyu'
    , 'kikuyu'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kin'
    , 'kin'
    , 'rw'
    , 'Kinyarwanda'
    , 'rwanda'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kir'
    , 'kir'
    , 'ky'
    , 'Kirghiz; Kyrgyz'
    , 'kirghiz'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kmb'
    , 'kmb'
    , null
    , 'Kimbundu'
    , 'kimbundu'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kok'
    , 'kok'
    , null
    , 'Konkani'
    , 'konkani'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kom'
    , 'kom'
    , 'kv'
    , 'Komi'
    , 'kom'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kon'
    , 'kon'
    , 'kg'
    , 'Kongo'
    , 'kongo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kor'
    , 'kor'
    , 'ko'
    , 'Korean'
    , 'coréen'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kos'
    , 'kos'
    , null
    , 'Kosraean'
    , 'kosrae'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kpe'
    , 'kpe'
    , null
    , 'Kpelle'
    , 'kpellé'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'krc'
    , 'krc'
    , null
    , 'Karachay-Balkar'
    , 'karatchai balkar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'krl'
    , 'krl'
    , null
    , 'Karelian'
    , 'carélien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kro'
    , 'kro'
    , null
    , 'Kru languages'
    , 'krou, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kru'
    , 'kru'
    , null
    , 'Kurukh'
    , 'kurukh'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kua'
    , 'kua'
    , 'kj'
    , 'Kuanyama; Kwanyama'
    , 'kuanyama; kwanyama'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kum'
    , 'kum'
    , null
    , 'Kumyk'
    , 'koumyk'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kur'
    , 'kur'
    , 'ku'
    , 'Kurdish'
    , 'kurde'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'kut'
    , 'kut'
    , null
    , 'Kutenai'
    , 'kutenai'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lad'
    , 'lad'
    , null
    , 'Ladino'
    , 'judéo-espagnol'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lah'
    , 'lah'
    , null
    , 'Lahnda'
    , 'lahnda'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lam'
    , 'lam'
    , null
    , 'Lamba'
    , 'lamba'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lao'
    , 'lao'
    , 'lo'
    , 'Lao'
    , 'lao'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lat'
    , 'lat'
    , 'la'
    , 'Latin'
    , 'latin'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lav'
    , 'lav'
    , 'lv'
    , 'Latvian'
    , 'letton'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lez'
    , 'lez'
    , null
    , 'Lezghian'
    , 'lezghien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lim'
    , 'lim'
    , 'li'
    , 'Limburgan; Limburger; Limburgish'
    , 'limbourgeois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lin'
    , 'lin'
    , 'ln'
    , 'Lingala'
    , 'lingala'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lit'
    , 'lit'
    , 'lt'
    , 'Lithuanian'
    , 'lituanien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lol'
    , 'lol'
    , null
    , 'Mongo'
    , 'mongo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'loz'
    , 'loz'
    , null
    , 'Lozi'
    , 'lozi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ltz'
    , 'ltz'
    , 'lb'
    , 'Luxembourgish; Letzeburgesch'
    , 'luxembourgeois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lua'
    , 'lua'
    , null
    , 'Luba-Lulua'
    , 'luba-lulua'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lub'
    , 'lub'
    , 'lu'
    , 'Luba-Katanga'
    , 'luba-katanga'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lug'
    , 'lug'
    , 'lg'
    , 'Ganda'
    , 'ganda'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lui'
    , 'lui'
    , null
    , 'Luiseno'
    , 'luiseno'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lun'
    , 'lun'
    , null
    , 'Lunda'
    , 'lunda'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'luo'
    , 'luo'
    , null
    , 'Luo (Kenya and Tanzania)'
    , 'luo (Kenya et Tanzanie)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'lus'
    , 'lus'
    , null
    , 'Lushai'
    , 'lushai'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mkd'
    , 'mac'
    , 'mk'
    , 'Macedonian'
    , 'macédonien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mad'
    , 'mad'
    , null
    , 'Madurese'
    , 'madourais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mag'
    , 'mag'
    , null
    , 'Magahi'
    , 'magahi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mah'
    , 'mah'
    , 'mh'
    , 'Marshallese'
    , 'marshall'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mai'
    , 'mai'
    , null
    , 'Maithili'
    , 'maithili'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mak'
    , 'mak'
    , null
    , 'Makasar'
    , 'makassar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mal'
    , 'mal'
    , 'ml'
    , 'Malayalam'
    , 'malayalam'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'man'
    , 'man'
    , null
    , 'Mandingo'
    , 'mandingue'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mri'
    , 'mao'
    , 'mi'
    , 'Maori'
    , 'maori'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'map'
    , 'map'
    , null
    , 'Austronesian languages'
    , 'austronésiennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mar'
    , 'mar'
    , 'mr'
    , 'Marathi'
    , 'marathe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mas'
    , 'mas'
    , null
    , 'Masai'
    , 'massaï'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'msa'
    , 'may'
    , 'ms'
    , 'Malay'
    , 'malais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mdf'
    , 'mdf'
    , null
    , 'Moksha'
    , 'moksa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mdr'
    , 'mdr'
    , null
    , 'Mandar'
    , 'mandar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'men'
    , 'men'
    , null
    , 'Mende'
    , 'mendé'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mga'
    , 'mga'
    , null
    , 'Irish, Middle (900-1200)'
    , 'irlandais moyen (900-1200)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mic'
    , 'mic'
    , null
    , 'Mi''kmaq; Micmac'
    , 'mi''kmaq; micmac'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'min'
    , 'min'
    , null
    , 'Minangkabau'
    , 'minangkabau'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mis'
    , 'mis'
    , null
    , 'Uncoded languages'
    , 'langues non codées'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mkh'
    , 'mkh'
    , null
    , 'Mon-Khmer languages'
    , 'môn-khmer, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mlg'
    , 'mlg'
    , 'mg'
    , 'Malagasy'
    , 'malgache'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mlt'
    , 'mlt'
    , 'mt'
    , 'Maltese'
    , 'maltais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mnc'
    , 'mnc'
    , null
    , 'Manchu'
    , 'mandchou'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mni'
    , 'mni'
    , null
    , 'Manipuri'
    , 'manipuri'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mno'
    , 'mno'
    , null
    , 'Manobo languages'
    , 'manobo, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'moh'
    , 'moh'
    , null
    , 'Mohawk'
    , 'mohawk'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mon'
    , 'mon'
    , 'mn'
    , 'Mongolian'
    , 'mongol'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mos'
    , 'mos'
    , null
    , 'Mossi'
    , 'moré'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mul'
    , 'mul'
    , null
    , 'Multiple languages'
    , 'multilingue'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mun'
    , 'mun'
    , null
    , 'Munda languages'
    , 'mounda, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mus'
    , 'mus'
    , null
    , 'Creek'
    , 'muskogee'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mwl'
    , 'mwl'
    , null
    , 'Mirandese'
    , 'mirandais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'mwr'
    , 'mwr'
    , null
    , 'Marwari'
    , 'marvari'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'myn'
    , 'myn'
    , null
    , 'Mayan languages'
    , 'maya, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'myv'
    , 'myv'
    , null
    , 'Erzya'
    , 'erza'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nah'
    , 'nah'
    , null
    , 'Nahuatl languages'
    , 'nahuatl, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nai'
    , 'nai'
    , null
    , 'North American Indian languages'
    , 'nord-amérindiennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nap'
    , 'nap'
    , null
    , 'Neapolitan'
    , 'napolitain'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nau'
    , 'nau'
    , 'na'
    , 'Nauru'
    , 'nauruan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nav'
    , 'nav'
    , 'nv'
    , 'Navajo; Navaho'
    , 'navaho'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nbl'
    , 'nbl'
    , 'nr'
    , 'Ndebele, South; South Ndebele'
    , 'ndébélé du Sud'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nde'
    , 'nde'
    , 'nd'
    , 'Ndebele, North; North Ndebele'
    , 'ndébélé du Nord'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ndo'
    , 'ndo'
    , 'ng'
    , 'Ndonga'
    , 'ndonga'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nds'
    , 'nds'
    , null
    , 'Low German; Low Saxon; German, Low; Saxon, Low'
    , 'bas allemand; bas saxon; allemand, bas; saxon, bas'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nep'
    , 'nep'
    , 'ne'
    , 'Nepali'
    , 'népalais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'new'
    , 'new'
    , null
    , 'Nepal Bhasa; Newari'
    , 'nepal bhasa; newari'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nia'
    , 'nia'
    , null
    , 'Nias'
    , 'nias'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nic'
    , 'nic'
    , null
    , 'Niger-Kordofanian languages'
    , 'nigéro-kordofaniennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'niu'
    , 'niu'
    , null
    , 'Niuean'
    , 'niué'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nno'
    , 'nno'
    , 'nn'
    , 'Norwegian Nynorsk; Nynorsk, Norwegian'
    , 'norvégien nynorsk; nynorsk, norvégien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nob'
    , 'nob'
    , 'nb'
    , 'Bokmål, Norwegian; Norwegian Bokmål'
    , 'norvégien bokmål'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nog'
    , 'nog'
    , null
    , 'Nogai'
    , 'nogaï; nogay'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'non'
    , 'non'
    , null
    , 'Norse, Old'
    , 'norrois, vieux'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nor'
    , 'nor'
    , 'no'
    , 'Norwegian'
    , 'norvégien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nqo'
    , 'nqo'
    , null
    , 'N''Ko'
    , 'n''ko'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nso'
    , 'nso'
    , null
    , 'Pedi; Sepedi; Northern Sotho'
    , 'pedi; sepedi; sotho du Nord'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nub'
    , 'nub'
    , null
    , 'Nubian languages'
    , 'nubiennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nwc'
    , 'nwc'
    , null
    , 'Classical Newari; Old Newari; Classical Nepal Bhasa'
    , 'newari classique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nya'
    , 'nya'
    , 'ny'
    , 'Chichewa; Chewa; Nyanja'
    , 'chichewa; chewa; nyanja'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nym'
    , 'nym'
    , null
    , 'Nyamwezi'
    , 'nyamwezi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nyn'
    , 'nyn'
    , null
    , 'Nyankole'
    , 'nyankolé'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nyo'
    , 'nyo'
    , null
    , 'Nyoro'
    , 'nyoro'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'nzi'
    , 'nzi'
    , null
    , 'Nzima'
    , 'nzema'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'oci'
    , 'oci'
    , 'oc'
    , 'Occitan (post 1500); Provençal'
    , 'occitan (après 1500); provençal'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'oji'
    , 'oji'
    , 'oj'
    , 'Ojibwa'
    , 'ojibwa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ori'
    , 'ori'
    , 'or'
    , 'Oriya'
    , 'oriya'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'orm'
    , 'orm'
    , 'om'
    , 'Oromo'
    , 'galla'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'osa'
    , 'osa'
    , null
    , 'Osage'
    , 'osage'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'oss'
    , 'oss'
    , 'os'
    , 'Ossetian; Ossetic'
    , 'ossète'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ota'
    , 'ota'
    , null
    , 'Turkish, Ottoman (1500-1928)'
    , 'turc ottoman (1500-1928)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'oto'
    , 'oto'
    , null
    , 'Otomian languages'
    , 'otomi, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'paa'
    , 'paa'
    , null
    , 'Papuan languages'
    , 'papoues, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pag'
    , 'pag'
    , null
    , 'Pangasinan'
    , 'pangasinan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pal'
    , 'pal'
    , null
    , 'Pahlavi'
    , 'pahlavi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pam'
    , 'pam'
    , null
    , 'Pampanga; Kapampangan'
    , 'pampangan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pan'
    , 'pan'
    , 'pa'
    , 'Panjabi; Punjabi'
    , 'pendjabi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pap'
    , 'pap'
    , null
    , 'Papiamento'
    , 'papiamento'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pau'
    , 'pau'
    , null
    , 'Palauan'
    , 'palau'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'peo'
    , 'peo'
    , null
    , 'Persian, Old (ca.600-400 B.C.)'
    , 'perse, vieux (ca. 600-400 av. J.-C.)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'fas'
    , 'per'
    , 'fa'
    , 'Persian'
    , 'persan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'phi'
    , 'phi'
    , null
    , 'Philippine languages'
    , 'philippines, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'phn'
    , 'phn'
    , null
    , 'Phoenician'
    , 'phénicien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pli'
    , 'pli'
    , 'pi'
    , 'Pali'
    , 'pali'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pol'
    , 'pol'
    , 'pl'
    , 'Polish'
    , 'polonais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pon'
    , 'pon'
    , null
    , 'Pohnpeian'
    , 'pohnpei'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'por'
    , 'por'
    , 'pt'
    , 'Portuguese'
    , 'portugais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pra'
    , 'pra'
    , null
    , 'Prakrit languages'
    , 'prâkrit, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pro'
    , 'pro'
    , null
    , 'Provençal, Old (to 1500)'
    , 'provençal ancien (jusqu''à 1500)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'pus'
    , 'pus'
    , 'ps'
    , 'Pushto; Pashto'
    , 'pachto'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'que'
    , 'que'
    , 'qu'
    , 'Quechua'
    , 'quechua'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'raj'
    , 'raj'
    , null
    , 'Rajasthani'
    , 'rajasthani'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'rap'
    , 'rap'
    , null
    , 'Rapanui'
    , 'rapanui'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'rar'
    , 'rar'
    , null
    , 'Rarotongan; Cook Islands Maori'
    , 'rarotonga; maori des îles Cook'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'roa'
    , 'roa'
    , null
    , 'Romance languages'
    , 'romanes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'roh'
    , 'roh'
    , 'rm'
    , 'Romansh'
    , 'romanche'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'rom'
    , 'rom'
    , null
    , 'Romany'
    , 'tsigane'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ron'
    , 'rum'
    , 'ro'
    , 'Romanian; Moldavian; Moldovan'
    , 'roumain; moldave'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'run'
    , 'run'
    , 'rn'
    , 'Rundi'
    , 'rundi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'rup'
    , 'rup'
    , null
    , 'Aromanian; Arumanian; Macedo-Romanian'
    , 'aroumain; macédo-roumain'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'rus'
    , 'rus'
    , 'ru'
    , 'Russian'
    , 'russe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sad'
    , 'sad'
    , null
    , 'Sandawe'
    , 'sandawe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sag'
    , 'sag'
    , 'sg'
    , 'Sango'
    , 'sango'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sah'
    , 'sah'
    , null
    , 'Yakut'
    , 'iakoute'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sai'
    , 'sai'
    , null
    , 'South American Indian (Other)'
    , 'indiennes d''Amérique du Sud, autres langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sal'
    , 'sal'
    , null
    , 'Salishan languages'
    , 'salishennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sam'
    , 'sam'
    , null
    , 'Samaritan Aramaic'
    , 'samaritain'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'san'
    , 'san'
    , 'sa'
    , 'Sanskrit'
    , 'sanskrit'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sas'
    , 'sas'
    , null
    , 'Sasak'
    , 'sasak'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sat'
    , 'sat'
    , null
    , 'Santali'
    , 'santal'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'scn'
    , 'scn'
    , null
    , 'Sicilian'
    , 'sicilien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sco'
    , 'sco'
    , null
    , 'Scots'
    , 'écossais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sel'
    , 'sel'
    , null
    , 'Selkup'
    , 'selkoupe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sem'
    , 'sem'
    , null
    , 'Semitic languages'
    , 'sémitiques, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sga'
    , 'sga'
    , null
    , 'Irish, Old (to 900)'
    , 'irlandais ancien (jusqu''à 900)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sgn'
    , 'sgn'
    , null
    , 'Sign Languages'
    , 'langues des signes'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'shn'
    , 'shn'
    , null
    , 'Shan'
    , 'chan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sid'
    , 'sid'
    , null
    , 'Sidamo'
    , 'sidamo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sin'
    , 'sin'
    , 'si'
    , 'Sinhala; Sinhalese'
    , 'singhalais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sio'
    , 'sio'
    , null
    , 'Siouan languages'
    , 'sioux, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sit'
    , 'sit'
    , null
    , 'Sino-Tibetan languages'
    , 'sino-tibétaines, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sla'
    , 'sla'
    , null
    , 'Slavic languages'
    , 'slaves, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'slk'
    , 'slo'
    , 'sk'
    , 'Slovak'
    , 'slovaque'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'slv'
    , 'slv'
    , 'sl'
    , 'Slovenian'
    , 'slovène'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sma'
    , 'sma'
    , null
    , 'Southern Sami'
    , 'sami du Sud'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sme'
    , 'sme'
    , 'se'
    , 'Northern Sami'
    , 'sami du Nord'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'smi'
    , 'smi'
    , null
    , 'Sami languages'
    , 'sames, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'smj'
    , 'smj'
    , null
    , 'Lule Sami'
    , 'sami de Lule'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'smn'
    , 'smn'
    , null
    , 'Inari Sami'
    , 'sami d''Inari'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'smo'
    , 'smo'
    , 'sm'
    , 'Samoan'
    , 'samoan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sms'
    , 'sms'
    , null
    , 'Skolt Sami'
    , 'sami skolt'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sna'
    , 'sna'
    , 'sn'
    , 'Shona'
    , 'shona'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'snd'
    , 'snd'
    , 'sd'
    , 'Sindhi'
    , 'sindhi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'snk'
    , 'snk'
    , null
    , 'Soninke'
    , 'soninké'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sog'
    , 'sog'
    , null
    , 'Sogdian'
    , 'sogdien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'som'
    , 'som'
    , 'so'
    , 'Somali'
    , 'somali'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'son'
    , 'son'
    , null
    , 'Songhai languages'
    , 'songhai, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sot'
    , 'sot'
    , 'st'
    , 'Sotho, Southern'
    , 'sotho du Sud'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'spa'
    , 'spa'
    , 'es'
    , 'Spanish; Castilian'
    , 'espagnol; castillan'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'srd'
    , 'srd'
    , 'sc'
    , 'Sardinian'
    , 'sarde'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'srn'
    , 'srn'
    , null
    , 'Sranan Tongo'
    , 'sranan tongo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'srp'
    , 'srp'
    , 'sr'
    , 'Serbian'
    , 'serbe'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'srr'
    , 'srr'
    , null
    , 'Serer'
    , 'sérère'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ssa'
    , 'ssa'
    , null
    , 'Nilo-Saharan languages'
    , 'nilo-sahariennes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ssw'
    , 'ssw'
    , 'ss'
    , 'Swati'
    , 'swati'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'suk'
    , 'suk'
    , null
    , 'Sukuma'
    , 'sukuma'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sun'
    , 'sun'
    , 'su'
    , 'Sundanese'
    , 'soundanais'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sus'
    , 'sus'
    , null
    , 'Susu'
    , 'soussou'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'sux'
    , 'sux'
    , null
    , 'Sumerian'
    , 'sumérien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'swa'
    , 'swa'
    , 'sw'
    , 'Swahili'
    , 'swahili'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'swe'
    , 'swe'
    , 'sv'
    , 'Swedish'
    , 'suédois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'syc'
    , 'syc'
    , null
    , 'Classical Syriac'
    , 'syriaque classique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'syr'
    , 'syr'
    , null
    , 'Syriac'
    , 'syriaque'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tah'
    , 'tah'
    , 'ty'
    , 'Tahitian'
    , 'tahitien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tai'
    , 'tai'
    , null
    , 'Tai languages'
    , 'tai, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tam'
    , 'tam'
    , 'ta'
    , 'Tamil'
    , 'tamoul'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tat'
    , 'tat'
    , 'tt'
    , 'Tatar'
    , 'tatar'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tel'
    , 'tel'
    , 'te'
    , 'Telugu'
    , 'télougou'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tem'
    , 'tem'
    , null
    , 'Timne'
    , 'temne'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ter'
    , 'ter'
    , null
    , 'Tereno'
    , 'tereno'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tet'
    , 'tet'
    , null
    , 'Tetum'
    , 'tetum'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tgk'
    , 'tgk'
    , 'tg'
    , 'Tajik'
    , 'tadjik'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tgl'
    , 'tgl'
    , 'tl'
    , 'Tagalog'
    , 'tagalog'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tha'
    , 'tha'
    , 'th'
    , 'Thai'
    , 'thaï'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'bod'
    , 'tib'
    , 'bo'
    , 'Tibetan'
    , 'tibétain'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tig'
    , 'tig'
    , null
    , 'Tigre'
    , 'tigré'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tir'
    , 'tir'
    , 'ti'
    , 'Tigrinya'
    , 'tigrigna'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tiv'
    , 'tiv'
    , null
    , 'Tiv'
    , 'tiv'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tkl'
    , 'tkl'
    , null
    , 'Tokelau'
    , 'tokelau'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tlh'
    , 'tlh'
    , null
    , 'Klingon; tlhIngan-Hol'
    , 'klingon'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tli'
    , 'tli'
    , null
    , 'Tlingit'
    , 'tlingit'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tmh'
    , 'tmh'
    , null
    , 'Tamashek'
    , 'tamacheq'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tog'
    , 'tog'
    , null
    , 'Tonga (Nyasa)'
    , 'tonga (Nyasa)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ton'
    , 'ton'
    , 'to'
    , 'Tonga (Tonga Islands)'
    , 'tongan (Îles Tonga)'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tpi'
    , 'tpi'
    , null
    , 'Tok Pisin'
    , 'tok pisin'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tsi'
    , 'tsi'
    , null
    , 'Tsimshian'
    , 'tsimshian'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tsn'
    , 'tsn'
    , 'tn'
    , 'Tswana'
    , 'tswana'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tso'
    , 'tso'
    , 'ts'
    , 'Tsonga'
    , 'tsonga'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tuk'
    , 'tuk'
    , 'tk'
    , 'Turkmen'
    , 'turkmène'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tum'
    , 'tum'
    , null
    , 'Tumbuka'
    , 'tumbuka'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tup'
    , 'tup'
    , null
    , 'Tupi languages'
    , 'tupi, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tur'
    , 'tur'
    , 'tr'
    , 'Turkish'
    , 'turc'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tut'
    , 'tut'
    , null
    , 'Altaic languages'
    , 'altaïques, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tvl'
    , 'tvl'
    , null
    , 'Tuvalu'
    , 'tuvalu'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'twi'
    , 'twi'
    , 'tw'
    , 'Twi'
    , 'twi'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'tyv'
    , 'tyv'
    , null
    , 'Tuvinian'
    , 'touva'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'udm'
    , 'udm'
    , null
    , 'Udmurt'
    , 'oudmourte'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'uga'
    , 'uga'
    , null
    , 'Ugaritic'
    , 'ougaritique'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'uig'
    , 'uig'
    , 'ug'
    , 'Uighur; Uyghur'
    , 'ouïgour'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ukr'
    , 'ukr'
    , 'uk'
    , 'Ukrainian'
    , 'ukrainien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'umb'
    , 'umb'
    , null
    , 'Umbundu'
    , 'umbundu'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'und'
    , 'und'
    , null
    , 'Undetermined'
    , 'indéterminée'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'urd'
    , 'urd'
    , 'ur'
    , 'Urdu'
    , 'ourdou'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'uzb'
    , 'uzb'
    , 'uz'
    , 'Uzbek'
    , 'ouszbek'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'vai'
    , 'vai'
    , null
    , 'Vai'
    , 'vaï'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ven'
    , 'ven'
    , 've'
    , 'Venda'
    , 'venda'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'vie'
    , 'vie'
    , 'vi'
    , 'Vietnamese'
    , 'vietnamien'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'vol'
    , 'vol'
    , 'vo'
    , 'Volapük'
    , 'volapük'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'vot'
    , 'vot'
    , null
    , 'Votic'
    , 'vote'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'wak'
    , 'wak'
    , null
    , 'Wakashan languages'
    , 'wakashanes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'wal'
    , 'wal'
    , null
    , 'Walamo'
    , 'walamo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'war'
    , 'war'
    , null
    , 'Waray'
    , 'waray'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'was'
    , 'was'
    , null
    , 'Washo'
    , 'washo'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'cym'
    , 'wel'
    , 'cy'
    , 'Welsh'
    , 'gallois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'wen'
    , 'wen'
    , null
    , 'Sorbian languages'
    , 'sorabes, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'wln'
    , 'wln'
    , 'wa'
    , 'Walloon'
    , 'wallon'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'wol'
    , 'wol'
    , 'wo'
    , 'Wolof'
    , 'wolof'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'xal'
    , 'xal'
    , null
    , 'Kalmyk; Oirat'
    , 'kalmouk; oïrat'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'xho'
    , 'xho'
    , 'xh'
    , 'Xhosa'
    , 'xhosa'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'yao'
    , 'yao'
    , null
    , 'Yao'
    , 'yao'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'yap'
    , 'yap'
    , null
    , 'Yapese'
    , 'yapois'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'yid'
    , 'yid'
    , 'yi'
    , 'Yiddish'
    , 'yiddish'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'yor'
    , 'yor'
    , 'yo'
    , 'Yoruba'
    , 'yoruba'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'ypk'
    , 'ypk'
    , null
    , 'Yupik languages'
    , 'yupik, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zap'
    , 'zap'
    , null
    , 'Zapotec'
    , 'zapotèque'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zbl'
    , 'zbl'
    , null
    , 'Blissymbols; Blissymbolics; Bliss'
    , 'symboles Bliss; Bliss'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zen'
    , 'zen'
    , null
    , 'Zenaga'
    , 'zenaga'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zgh'
    , 'zgh'
    , null
    , 'Standard Moroccan Tamazight'
    , 'amazighe standard marocain'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zha'
    , 'zha'
    , 'za'
    , 'Zhuang; Chuang'
    , 'zhuang; chuang'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'znd'
    , 'znd'
    , null
    , 'Zande languages'
    , 'zandé, langues'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zul'
    , 'zul'
    , 'zu'
    , 'Zulu'
    , 'zoulou'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zun'
    , 'zun'
    , null
    , 'Zuni'
    , 'zuni'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zxx'
    , 'zxx'
    , null
    , 'No linguistic content; Not applicable'
    , 'pas de contenu linguistique; non applicable'
  );
insert into base.language (code,iso_3b,iso_2,eng_name,fra_name) values (
      'zza'
    , 'zza'
    , null
    , 'Zaza; Dimili; Dimli; Kirdki; Kirmanjki; Zazaki'
    , 'zaza; dimili; dimli; kirdki; kirmanjki; zazaki'
  );
select base.priv_grants();
insert into base.parm_v (module,parm,type,value,cmt) values 
  ('mychips','user_port','int','12345','Default port where mobile user application connects.')
 ,('mychips','user_inet','text','192.168.56.101','Default IP where mobile application connects.')
 ,('mychips','cert_days','int','14','Default number of days for a certificate to be valid.')

 ,('mychips','site_ent','int', 0,'The ID number of the entity on this site that is the primary administrator.  Internal lifts will be signed by this entity.')

 ,('lifts','order','text', 'bang desc', 'An order-by clause to describe how to prioritize lifts when selecting them from the pathways view.  The first result of the query will be the first lift performed.')
 ,('lifts','interval','int', 10000,'The number of milliseconds between sending requests to the database to choose and conduct a lift')
 ,('lifts','limit','int', 1,'The maximum number of lifts the database may perform per request cycle')
 ,('lifts','minimum','int', 10000,'The smallest number of units to consider lifting, absent other guidance from the user or his tallies')
;
