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
create function mychips.chit_state(isdebit boolean, request text, signature text) returns text immutable language plpgsql as $$
    begin return
      case when isdebit() then
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
           when request = 'userAccept'		then 'userAgree'
           when request = 'userDraft'		then 'userDraft'
           when request is null			then 'userValid'
      else     					     'undefined'	end
      end;
    end;
$$;
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
  , com_name	varchar		not null unique
  , capital	varchar
  , cur_code	varchar(4)	not null
  , cur_name	varchar		not null 
  , dial_code	varchar(20)
  , iso_3	varchar(4)	not null unique
  , iana	varchar(6)
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
create table mychips.covenants (
author	varchar
  , title	varchar
  , version	int
  , language	varchar		, primary key(author, title, version, language)
  , released	date
  , content	varchar
  , hash	varchar		, unique (hash)
);
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
create table base.ent (
id		int		check (id > 0) primary key
  , ent_type	varchar(1)	not null default 'p' check(ent_type in ('p','o','g','r'))
  , ent_name	varchar		not null
  , fir_name	varchar		constraint "!base.ent.CFN" check(case when ent_type != 'p' then fir_name is null end)
  , mid_name	varchar		constraint "!base.ent.CMN" check(case when fir_name is null then mid_name is null end)
  , pref_name	varchar		constraint "!base.ent.CPN" check(case when fir_name is null then pref_name is null end)
  , title	varchar		constraint "!base.ent.CTI" check(case when fir_name is null then title is null end)
  , gender	varchar(1)	constraint "!base.ent.CGN" check(case when ent_type != 'p' then gender is null end)
  , marital	varchar(1)	constraint "!base.ent.CMS" check(case when ent_type != 'p' then marital is null end)
  , ent_cmt	varchar
  , born_date	date		constraint "!base.ent.CBD" check(case when ent_type = 'p' and inside then born_date is not null end)
  , username	varchar		unique
  , database	boolean		not null default false
  , ent_inact	boolean		not null default false
  , inside	boolean		not null default true
  , country	varchar(3)	not null default 'US' references base.country on update cascade
  , tax_id	varchar       , unique(country, tax_id)
  , bank	varchar
  , proxy	int		constraint "!ent.ent.OPR" check (proxy != id)


    
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
  from		wm.column_data cd
    left join	wm.column_text nt	on nt.ct_sch = cd.nat_sch and nt.ct_tab = cd.nat_tab and nt.ct_col = cd.nat_col
    left join	wm.column_text ct	on ct.ct_sch = cd.cdt_sch and ct.ct_tab = cd.cdt_tab and ct.ct_col = cd.cdt_col and ct.language = nt.language

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
addr_ent	int		references base.ent on update cascade on delete cascade
  , addr_seq	int	      , primary key (addr_ent, addr_seq)
  , addr_spec	varchar		not null
  , addr_type	varchar		not null check(addr_type in ('bill','ship'))
  , addr_prim	boolean		not null default false constraint "!base.addr.CPA" check(case when addr_inact is true then addr_prim is false end)
  , addr_cmt	varchar
  , addr_inact	boolean		not null default false
  , city	varchar
  , state	varchar
  , pcode	varchar
  , country	varchar(3)	constraint "!base.addr.CCO" not null default 'US' references base.country on update cascade
  , unique (addr_ent, addr_seq, addr_type)		-- Needed for addr_prim FK to work

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table base.comm (
comm_ent	int		references base.ent on update cascade on delete cascade
  , comm_seq	int	      , primary key (comm_ent, comm_seq)
  , comm_spec	varchar
  , comm_type	varchar		not null check(comm_type in ('phone','email','cell','fax','text','web','pager','other'))
  , comm_prim	boolean		not null default false constraint "!base.comm.CPC" check(case when comm_inact is true then comm_prim is false end)
  , comm_cmt	varchar
  , comm_inact	boolean		not null default false
  , unique (comm_ent, comm_seq, comm_type)		-- Needed for comm_prim FK to work

    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.curr_eid() returns int language sql security definer stable as $$
    select id from base.ent where username = session_user;
$$;
create table base.ent_audit (
id int
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
org		int4		references base.ent on update cascade
  , mem		int4		references base.ent on update cascade on delete cascade
  , primary key (org, mem)
  , role	varchar
  , supr_path	int[]		-- other modules (like empl) are responsible to maintain this cached field
    
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
    begin
        if TG_OP = 'UPDATE' then
            if new.inside != old.inside then 	-- if changing inside/outside (shouldn't happen except by someone who knows what he is doing)
                new.id := null;
            end if;
        end if;
        if new.id is null then
            if new.ent_type = 'p' then		-- use separate range for people, companies, groups, roles
                select into new.id coalesce(max(id)+1,10000) from base.ent where id >= 10000;
            elseif new.ent_type = 'g' then
                select into new.id coalesce(max(id)+1,1000) from base.ent where id >= 1000 and id < 10000;
            elseif new.ent_type = 'o' then
                select into new.id coalesce(max(id)+1,100) from base.ent where id >= 100 and id < 1000;
            else
                select into new.id coalesce(max(id)+1,1) from base.ent where id >= 1 and id < 100;
            end if;
        end if;
        return new;
    end;
$$;
create function base.ent_tf_iuacc() returns trigger language plpgsql security definer as $$
    declare
      trec	record;
    begin
      if new.username is null then		-- Can't have database access without a username
        new.database := false;
      end if;
      if TG_OP = 'UPDATE' then
        if new.username != old.username then	-- if trying to change an existing username

          execute 'drop user ' || '"' || old.username || '"';
        end if;
      end if;

      if new.database and not exists (select usename from pg_shadow where usename = new.username) then

        execute 'create user ' || '"' || new.username || '"';
        for trec in select * from base.priv where grantee = new.username loop
          execute 'grant "' || trec.priv_level || '" to ' || trec.grantee;
        end loop;
      elseif not new.database and exists (select usename from pg_shadow where usename = new.username) then

        execute 'drop user ' || '"' || new.username || '"';
      end if;
      return new;
    end;
$$;
create view base.ent_v as select e.id, e.ent_name, e.ent_type, e.ent_cmt, e.fir_name, e.mid_name, e.pref_name, e.title, e.gender, e.marital, e.born_date, e.username, e.database, e.ent_inact, e.inside, e.country, e.tax_id, e.bank, e.proxy, e.crt_by, e.mod_by, e.crt_date, e.mod_date
      , case when e.fir_name is null then e.ent_name else e.ent_name || ', ' || coalesce(e.pref_name,e.fir_name) end	as std_name
      , e.ent_name || case when e.fir_name is not null then ', ' || 
                case when e.title is null then '' else e.title || ' ' end ||
                e.fir_name ||
                case when e.mid_name is null then '' else ' ' || e.mid_name end
            else '' end												as frm_name
      , case when e.fir_name is null then '' else coalesce(e.pref_name,e.fir_name) || ' ' end || e.ent_name	as cas_name
      , e.fir_name || case when e.mid_name is null then '' else ' ' || e.mid_name end				as giv_name
    from	base.ent	e;

    create rule base_ent_v_insert as on insert to base.ent_v
        do instead insert into base.ent (ent_name, ent_type, ent_cmt, fir_name, mid_name, pref_name, title, gender, marital, born_date, username, database, ent_inact, inside, country, tax_id, bank, proxy, crt_by, mod_by, crt_date, mod_date) values (new.ent_name, new.ent_type, new.ent_cmt, new.fir_name, new.mid_name, new.pref_name, new.title, new.gender, new.marital, new.born_date, new.username, new.database, new.ent_inact, new.inside, new.country, new.tax_id, new.bank, new.proxy, session_user, session_user, current_timestamp, current_timestamp);
    create rule base_ent_v_update as on update to base.ent_v
        do instead update base.ent set ent_name = new.ent_name, ent_type = new.ent_type, ent_cmt = new.ent_cmt, fir_name = new.fir_name, mid_name = new.mid_name, pref_name = new.pref_name, title = new.title, gender = new.gender, marital = new.marital, born_date = new.born_date, username = new.username, database = new.database, ent_inact = new.ent_inact, inside = new.inside, country = new.country, tax_id = new.tax_id, bank = new.bank, proxy = new.proxy, mod_by = session_user, mod_date = current_timestamp where id = old.id;
    create rule base_ent_v_delete as on delete to base.ent_v
        do instead delete from base.ent where id = old.id;
create index base_ent_x_ent_type on base.ent (ent_type);
create index base_ent_x_proxy on base.ent (proxy);
create index base_ent_x_username on base.ent (username);
create table base.parm (
module	varchar
  , parm	varchar
  , primary key (module, parm)
  , type	varchar		check (type in ('int','date','text','float','boolean'))
  , cmt		varchar
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
create function base.user_id(varchar) returns int language sql security definer stable as $$
    select id from base.ent where username = $1;
$$;
create function base.username(int) returns varchar language sql security definer stable as $$
    select username from base.ent where id = $1;
$$;
create table mychips.peers (
peer_ent	int		primary key references base.ent on update cascade on delete cascade
  , peer_cdi	varchar		
  , peer_hid	varchar		
  , peer_pub	varchar		
  , peer_inet	inet
  , peer_port	int
  , peer_cmt	varchar
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.tallies (
tally_ent	int		references base.ent on update cascade on delete cascade
  , tally_seq	int	      , primary key (tally_ent, tally_seq)
  , tally_guid	uuid		not null
  , tally_type	varchar		not null default 'stock' check(tally_type in ('stock','foil'))
  , tally_date	timestamptz	not null default current_timestamp
  , version	int		not null default 1 constraint "!mychips.tallies.VER" check (version > 0)
  , partner	int		references base.ent on update cascade on delete restrict
  , contract	varchar	     -- references mychips.covenants on update cascade on delete restrict
  , status	varchar		not null default 'void' check(status in ('void','draft','open','close'))
  , request	varchar		check(request is null or request in ('void','draft','open','close'))
  , comment	varchar
  , user_sig	varchar
  , part_sig	varchar
  , cr_limit	bigint		not null default 0 constraint "!mychips.tallies.FLM" check (cr_limit >= 0)
  , dr_limit	bigint		not null default 0 constraint "!mychips.tallies.RLM" check (dr_limit >= 0)
  , total_c	bigint		default 0 not null
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.tokens (
token_ent	int		references base.ent on update cascade on delete cascade
  , token_seq	int	      , primary key (token_ent, token_seq)
  , token	varchar		not null unique
  , allows	varchar		not null default 'stock' constraint "!mychips.tokens.ITA" check (allows in ('stock','foil','query','user'))
  , token_cmt	varchar		
  , used	boolean		not null default false
  , exp_date	timestamp(0)	default current_timestamp + '45 minutes'
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.users (
user_ent	int		primary key references base.ent on update cascade on delete cascade
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
  , array (select array[sw_name, sw_value] from wm.table_style ts where ts.ts_sch = td.td_sch and ts.ts_tab = td.td_tab order by sw_name) as styles
  , (select array_agg(to_jsonb(d)) from (select col, field, type, nonull, length, pkey, to_jsonb(values) as values, jsonb_object(styles) as styles from wm.column_meta cm where cm.sch = td.td_sch and cm.tab = td.td_tab) d) as columns
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
prim_ent	int
  , prim_seq	int
  , prim_type	varchar
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
create view base.addr_v_flat as select e.id, a0.addr_spec as "bill_addr", a0.city as "bill_city", a0.state as "bill_state", a0.pcode as "bill_pcode", a0.country as "bill_country", a1.addr_spec as "ship_addr", a1.city as "ship_city", a1.state as "ship_state", a1.pcode as "ship_pcode", a1.country as "ship_country" from base.ent e left join base.addr a0 on a0.addr_ent = e.id and a0.addr_type = 'bill' and a0.addr_prim left join base.addr a1 on a1.addr_ent = e.id and a1.addr_type = 'ship' and a1.addr_prim;
create index base_addr_x_addr_type on base.addr (addr_type);
create table base.comm_prim (
prim_ent	int
  , prim_seq	int
  , prim_type	varchar
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
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','database',old.database::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','ent_inact',old.ent_inact::varchar);
		insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'delete','inside',old.inside::varchar);
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
		if new.database is distinct from old.database then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','database',old.database::varchar); end if;
		if new.ent_inact is distinct from old.ent_inact then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','ent_inact',old.ent_inact::varchar); end if;
		if new.inside is distinct from old.inside then insert into base.ent_audit (id,a_date,a_by,a_action,a_column,a_value) values (old.id,transaction_timestamp(),session_user,'update','inside',old.inside::varchar); end if;
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
create view base.ent_v_pub as select id, std_name, ent_type, username, ent_inact, inside, crt_by, mod_by, crt_date, mod_date from base.ent_v;
create table base.parm_audit (
module varchar,parm varchar
          , a_seq	int		check (a_seq >= 0)
          , a_date	timestamptz	not null default current_timestamp
          , a_by	name		not null default session_user references base.ent (username) on update cascade
          , a_action	audit_type	not null default 'update'
          , a_column	varchar		not null
          , a_value	varchar
     	  , a_reason	text
          , primary key (module,parm,a_seq)
);
create function base.parm_boolean(m varchar, p varchar) returns boolean language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'boolean';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_boolean;
    end;
$$;
create function base.parm_date(m varchar, p varchar) returns date language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'date';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_date;
    end;
$$;
create function base.parm_float(m varchar, p varchar) returns float language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'float';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_float;
    end;
$$;
create function base.parm_int(m varchar, p varchar) returns int language plpgsql stable as $$
    declare
        r	record;
    begin
        select into r * from base.parm where module = m and parm = p and type = 'int';
        if not found then raise exception '!base.parm.PNF % %', m, p; end if;
        return r.v_int;
    end;
$$;
create function base.parmset(m varchar, p varchar, v anyelement, t varchar default null) returns anyelement language plpgsql as $$
    begin
      if exists (select type from base.parm where module = m and parm = p) then
        update base.parm_v set value = v where module = m and parm = p;
      else
        insert into base.parm_v (module,parm,value,type) values (m,p,v,t);
      end if;
      return v;
    end;
$$;
create function base.parm_text(m varchar, p varchar) returns int language plpgsql stable as $$
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
create function base.parm(m varchar, p varchar, d anyelement) returns anyelement language plpgsql stable as $$
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
create function base.priv_grants() returns int language plpgsql as $$
    declare
        erec	record;
        trec	record;
        cnt	int default 0;
    begin
        for erec in select * from base.ent where database and username is not null loop
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
  , e.database
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
create function base.std_name(int) returns varchar language sql security definer stable as $$
    select std_name from base.ent_v where id = $1;
$$;
create function base.std_name(name) returns varchar language sql security definer stable as $$
    select std_name from base.ent_v where username = $1;
$$;
create table mychips.chits (
chit_ent	int
  , chit_seq	int	      , foreign key (chit_ent, chit_seq) references mychips.tallies on update cascade on delete cascade
  , chit_idx	int	      , primary key (chit_ent, chit_seq, chit_idx)
  , chit_guid	uuid		not null
  , chit_type	varchar		not null default 'tran' check(chit_type in ('gift','lift','loan','tran'))
  , chit_date	timestamptz	not null default current_timestamp
  , request	varchar		check(request is null or request in ('userDraft','userRequest','userAgree','userDecline'))
  , signature	varchar
  , units	bigint		not null
  , pro_quo	varchar
  , memo	varchar
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create table mychips.comm_test (
test_ent		int
  , test_seq		int
  , test_dat		varchar
  , foreign key (test_ent, test_seq) references base.comm on update cascade on delete cascade
);
create table mychips.confirms (
conf_ent	int
  , conf_seq	int	      , foreign key (conf_ent, conf_seq) references mychips.tallies on update cascade on delete cascade
  , conf_idx	int	      , primary key (conf_ent, conf_seq, conf_idx)
  , conf_id	uuid
  , conf_date	timestamptz	not null default current_timestamp
  , sum		bigint		not null
  , signature	varchar
);
create view mychips.peers_v as select 
    ee.id, ee.ent_name, ee.ent_type, ee.ent_cmt, ee.fir_name, ee.mid_name, ee.pref_name, ee.title, ee.gender, ee.marital, ee.born_date, ee.username, ee.database, ee.ent_inact, ee.inside, ee.country, ee.tax_id, ee.bank, ee.proxy, ee.std_name, ee.frm_name, ee.giv_name, ee.cas_name
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
create function mychips.token_tf_seq() returns trigger security definer language plpgsql as $$
    begin
      if new.token_seq is null then
        select into new.token_seq coalesce(max(token_seq),0)+1 from mychips.tokens where token_ent = new.token_ent;
      end if;
      if new.token is null then				-- If no token specified
        loop
          select into new.token md5(random()::varchar);
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
    ee.id, ee.ent_name, ee.ent_type, ee.ent_cmt, ee.fir_name, ee.mid_name, ee.pref_name, ee.title, ee.gender, ee.marital, ee.born_date, ee.username, ee.database, ee.ent_inact, ee.inside, ee.country, ee.tax_id, ee.bank, ee.proxy, ee.std_name, ee.frm_name, ee.giv_name, ee.cas_name
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
  , component	varchar
  , access	varchar(5)	not null constraint "!wylib.data.IAT" check (access in ('priv', 'read', 'write'))
  , owner	int		not null default base.curr_eid() references base.ent on update cascade on delete cascade
  , data	jsonb
    
  , crt_date    timestamptz	not null default current_timestamp
  , mod_date    timestamptz	not null default current_timestamp
  , crt_by      name		not null default session_user references base.ent (username) on update cascade
  , mod_by	name		not null default session_user references base.ent (username) on update cascade

);
create function base.addr_make_prim(ent int, seq int, typ text) returns void language plpgsql security definer as $$
    begin

        update base.addr_prim set prim_seq = seq where prim_ent = ent and prim_type = typ;
        if not found then
            insert into base.addr_prim (prim_ent,prim_seq,prim_type) values (ent,seq,typ);
        end if;
    end;
$$;
create function base.addr_remove_prim(ent int, seq int, typ text) returns void language plpgsql security definer as $$
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
create function base.comm_make_prim(ent int, seq int, typ text) returns void language plpgsql security definer as $$
    begin

        update base.comm_prim set prim_seq = seq where prim_ent = ent and prim_type = typ;
        if not found then
            insert into base.comm_prim (prim_ent,prim_seq,prim_type) values (ent,seq,typ);
        end if;
    end;
$$;
create function base.comm_remove_prim(ent int, seq int, typ text) returns void language plpgsql security definer as $$
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
create function base.parmsett(m varchar, p varchar, v varchar, t varchar default null) returns varchar language plpgsql as $$
    begin
      return base.parmset(m,p,v,t);
    end;
$$;
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
create function base.parm(m varchar, p varchar) returns text language sql stable as $$ select value from base.parm_v where module = m and parm = p; $$;
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
        when new.type = 'text' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_text) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value);
        when new.type = 'float' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_float) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value::float);
        when new.type = 'boolean' then
            insert into base.parm (module, parm, type, cmt, crt_by, mod_by, crt_date, mod_date,v_boolean) values (new.module, new.parm, new.type, new.cmt, session_user, session_user, current_timestamp, current_timestamp, new.value::boolean);
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
create function mychips.confirms_tf_seq() returns trigger language plpgsql security definer as $$
    begin
        if new.conf_idx is null then
            select into new.conf_idx coalesce(max(conf_idx),0)+1 from mychips.confirms where conf_ent = new.conf_ent and conf_seq = new.conf_seq;
        end if;
        return new;
    end;
$$;
create function mychips.peer_sock(int) returns text stable language sql as $$
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
        insert into base.ent (ent_name,ent_type,ent_cmt,fir_name,mid_name,pref_name,title,gender,marital,born_date,username,database,ent_inact,inside,country,tax_id,bank,proxy,mod_by,mod_date) values (trec.ent_name,trec.ent_type,trec.ent_cmt,trec.fir_name,trec.mid_name,trec.pref_name,trec.title,trec.gender,trec.marital,trec.born_date,trec.username,trec.database,trec.ent_inact,trec.inside,trec.country,trec.tax_id,trec.bank,trec.proxy,session_user,current_timestamp) returning id into new.id;
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
    update base.ent set ent_name = new.ent_name,ent_cmt = new.ent_cmt,fir_name = new.fir_name,mid_name = new.mid_name,pref_name = new.pref_name,title = new.title,gender = new.gender,marital = new.marital,born_date = new.born_date,database = new.database,ent_inact = new.ent_inact,inside = new.inside,country = new.country,tax_id = new.tax_id,bank = new.bank,proxy = new.proxy,mod_by = session_user,mod_date = current_timestamp where id = old.id returning id into new.id;
    
    
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
    te.tally_ent, te.tally_seq, te.request, te.comment, te.cr_limit, te.dr_limit, te.tally_guid, te.tally_type, te.version, te.partner, te.contract, te.crt_by, te.mod_by, te.crt_date, te.mod_date, te.tally_date, te.status
  , ue.peer_cdi		as user_cdi
  , ue.peer_sock	as user_sock
  , ue.std_name		as user_name
  , te.user_sig
  , pe.peer_cdi		as part_cdi
  , pe.peer_sock	as part_sock
  , pe.std_name		as part_name
  , te.part_sig
  , mychips.tally_state(status,request,user_sig,part_sig,total_c) as state
  , mychips.tally_state(status,request,user_sig,part_sig,total_c) = any(array['peerProffer','closing']) as action
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
    )								as json

    from	mychips.tallies	te
    join	mychips.users_v	ue on ue.user_ent = te.tally_ent
    join	mychips.users_v	pe on pe.user_ent = te.partner;











;
create function mychips.tally_notices() returns void language plpgsql as $$
    declare
        trec		record;
    begin
        for trec in select * from mychips.tallies where request is not null loop
            perform mychips.tally_notice(trec);
        end loop;
        for trec in select * from mychips.chits where request is not null loop
            perform mychips.chit_notice(trec);
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
        insert into base.ent (ent_name,ent_type,ent_cmt,fir_name,mid_name,pref_name,title,gender,marital,born_date,username,database,ent_inact,inside,country,tax_id,bank,proxy,mod_by,mod_date) values (trec.ent_name,trec.ent_type,trec.ent_cmt,trec.fir_name,trec.mid_name,trec.pref_name,trec.title,trec.gender,trec.marital,trec.born_date,trec.username,trec.database,trec.ent_inact,trec.inside,trec.country,trec.tax_id,trec.bank,trec.proxy,session_user,current_timestamp) returning id into new.id;
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
    update base.ent set ent_name = new.ent_name,ent_cmt = new.ent_cmt,fir_name = new.fir_name,mid_name = new.mid_name,pref_name = new.pref_name,title = new.title,gender = new.gender,marital = new.marital,born_date = new.born_date,database = new.database,ent_inact = new.ent_inact,inside = new.inside,country = new.country,tax_id = new.tax_id,bank = new.bank,proxy = new.proxy,mod_by = session_user,mod_date = current_timestamp where id = old.id returning id into new.id;
    
    
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
create view wylib.data_v as select wd.component, wd.access, wd.data, wd.crt_by, wd.mod_by, wd.crt_date, wd.mod_date
      , oe.std_name

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
create view json.ticket as select
    u.id		as "id"
  , t.token_seq		as "seq"
  , case when t.allows = 'user' then u.user_sock
    else u.peer_cdi end	as "url"
  , t.token		as "token"
  , s.peer_pub		as "public"
  , t.exp_date		as "expires"

    from	mychips.users_v	u
    join	mychips.tokens	t on t.token_ent = u.id
    left join	base.parm	p on p.module = 'mychips' and p.parm = 'site_ent'
    left join	mychips.peers	s on s.peer_ent = p.v_int
    where	t.exp_date > current_timestamp;
create trigger mychips_chits_tr_seq before insert on mychips.chits for each row execute procedure mychips.chits_tf_seq();
create view mychips.chits_v as select 
    ch.chit_ent, ch.chit_seq, ch.chit_idx, ch.request, ch.signature, ch.units, ch.pro_quo, ch.memo, ch.chit_guid, ch.chit_type, ch.crt_by, ch.mod_by, ch.crt_date, ch.mod_date, ch.chit_date
  , te.user_cdi
  , te.part_cdi
  , te.tally_type
  , case when te.tally_type = 'stock' and ch.units >= 0 or te.tally_type = 'foil' and ch.units < 0 then 'debit' else 'credit' end		as effect
         
  , ch.units::float8 / 1000000.00	as value
  , ch.units::float8 * case when te.tally_type = 'stock' then 1 else -1 end / 1000000	as amount
  , mychips.chit_state(te.tally_type = 'stock' and ch.units >= 0 or te.tally_type = 'foil' and ch.units < 0, ch.request, ch.signature)	as state
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
create trigger mychips_peers_v_tr_ins instead of insert on mychips.peers_v for each row execute procedure mychips.peers_v_insfunc();
create trigger mychips_peers_v_tr_upd instead of update on mychips.peers_v for each row execute procedure mychips.peers_v_updfunc();
create function mychips.tally_notice(tally mychips.tallies) returns boolean language plpgsql security definer as $$
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
        entity		int;
        guid		uuid = obj->>'guid';
        curState	text;
        lrec		record;
        trec		record;
        tallyType text; notType text; partner int;
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
                using entity, guid, tallyType, (obj->>'version')::int, partner, obj->>'contract', 'draft', obj->'comment', obj->'signed'->>tallyType, obj->'signed'->>notType, coalesce((obj->>'crLimit')::bigint,0), coalesce((obj->>'drLimit')::bigint,0);
          else						-- Tally already exists, do update
            execute 'update mychips.tallies set version = $1, contract = $2, status = $3, comment = $4, user_sig = $5, part_sig = $6, cr_limit = $7, dr_limit = $8 where tally_ent = $9 and tally_seq = $10'
                using (obj->>'version')::int, obj->>'contract', 'draft', obj->'comment', obj->'signed'->>tallyType, obj->'signed'->>notType, coalesce((obj->>'crLimit')::bigint,0), coalesce((obj->>'drLimit')::bigint,0), trec.tally_ent, trec.tally_seq;
          end if;
        end if;

        if recipe ? 'update' then
          for lrec in select * from jsonb_each_text(recipe->'update') loop	--Fixme: should probably restrict which columns can be updated by this method

            execute 'update mychips.tallies set request = null, ' || lrec.key || ' = $1 where tally_ent = $2 and tally_seq = $3' using lrec.value, trec.tally_ent, trec.tally_seq;
          end loop;
          update mychips.tallies set request = null where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
        end if;


        select into trec tally_ent,tally_seq,state,action,json from mychips.tallies_v where tally_ent = trec.tally_ent and tally_seq = trec.tally_seq;
        if trec.action or (trec.state = 'open' and (curState is null or curState != 'open')) then	-- Also notify if changed to open status
raise notice '  notify for user %', trec.tally_ent;
            perform pg_notify('mychips_user', trec.json::text);
            perform pg_notify('mychips_user_'||trec.tally_ent::text, trec.json::text);
        end if;
        return trec.state;
    end;
$$;
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

            insert into wylib.data (component, access, data, crt_by, mod_by, crt_date, mod_date) values (new.component, new.access, new.data, session_user, session_user, current_timestamp, current_timestamp) returning into new.ruid ruid;
            return new;
        end;
    $$;
create function wylib.data_v_tf_upd() returns trigger language plpgsql security definer  as $$
        begin
           if not (old.owner = base.curr_eid() or old.access = 'write') then return null; end if;
            if ((new.access is not distinct from old.access) and (new.data is not distinct from old.data)) then return null; end if;
            update wylib.data set access = new.access, data = new.data, mod_by = session_user, mod_date = current_timestamp where ruid = old.ruid returning into new.ruid ruid;
            return new;
        end;
    $$;
create trigger base_addr_v_tr_ins instead of insert on base.addr_v for each row execute procedure base.addr_v_insfunc();
create trigger base_addr_v_tr_upd instead of update on base.addr_v for each row execute procedure base.addr_v_updfunc();
create trigger base_comm_v_tr_ins instead of insert on base.comm_v for each row execute procedure base.comm_v_insfunc();
create trigger base_comm_v_tr_upd instead of update on base.comm_v for each row execute procedure base.comm_v_updfunc();
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
raise notice 'Import data:%', data;
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

        select array_agg(cdt_col), string_agg(quote_ident(cdt_col),',') into fieldArray,fieldList from wm.column_data where cdt_sch = 'json' and cdt_tab = tableName;
        select array_to_string(pkey,',') into primKeyList from wm.table_data where td_sch = 'json' and td_tab = tableName;

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
create view json.users as select
  cdi, name, type, first, middle, prefer, begin, juris, taxid
  , (select array_agg(to_jsonb(d)) from (select spec,type,main,locale,state,post,comment,prior from json.address a where a.id = id order by seq) d) as addresses
  , (select array_agg(to_jsonb(d)) from (select spec,media,comment,prior from json.connect c where c.id = id order by seq) d) as connects
    from json.user;
create function mychips.chit_notice(chit mychips.chits) returns boolean language plpgsql security definer as $$
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
        jrec = jsonb_set(jrec, '{entity}', to_jsonb(new.chit_ent));
        jrec = jsonb_set(jrec, '{tally}', to_jsonb(trec.tally_guid));
        jrec = jsonb_set(jrec, '{action}', to_jsonb(act));
        jrec = jsonb_set(jrec, '{at}', to_jsonb(trec.part_sock));
        jrec = jsonb_set(jrec, '{object}', (select json from mychips.chits_v where chit_ent = new.chit_ent and chit_seq = new.chit_seq and chit_idx = new.chit_idx));
raise notice 'Chit notice:%', jrec::text;
        perform pg_notify(channel, jrec::text);
        return true;
    end;
$$;
create function mychips.chit_process(msg jsonb, recipe jsonb) returns text language plpgsql as $$
    declare
        cdi		text	= msg->>'user';
        obj		jsonb	= msg->'object';
        entity		int;
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
raise notice 'Chit cdi:% entity:% state:% recipe:%', cdi, entity, curState, recipe;
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
            
            execute 'insert into mychips.chits (chit_ent,chit_seq,chit_guid,chit_type,chit_date,signature,units,pro_quo,memo) values ($1,$2,$3,$4,current_timestamp,$5,$6,$7,$8)'
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

        select into curState state from mychips.chits_v where chit_ent = crec.chit_ent and chit_seq = crec.chit_seq and chit_idx = crec.chit_idx;
        return curState;
    end;
$$;
create function mychips.chits_tf_notice() returns trigger language plpgsql security definer as $$
    begin
raise notice 'Chit update';
        if (new.request is not null and new.request is distinct from old.request) then
            perform mychips.chit_notice(new);
        end if;
        return new;
    end;
$$;
create function mychips.tallies_tf_notice() returns trigger language plpgsql security definer as $$
    begin
        if (new.request is not null and new.request is distinct from old.request) then
            perform mychips.tally_notice(new);
        end if;
        return new;
    end;
$$;
create trigger mychips_tokens_v_tr_ins instead of insert on mychips.tokens_v for each row execute procedure mychips.tokens_v_insfunc();
create trigger mychips_tokens_v_tr_upd instead of update on mychips.tokens_v for each row execute procedure mychips.tokens_v_updfunc();
create trigger wylib_data_v_tr_del instead of delete on wylib.data_v for each row execute procedure wylib.data_v_tf_del();
create trigger wylib_data_v_tr_ins instead of insert on wylib.data_v for each row execute procedure wylib.data_v_tf_ins();
create trigger wylib_data_v_tr_upd instead of update on wylib.data_v for each row execute procedure wylib.data_v_tf_upd();
create trigger mychips_chits_tr_notice after update on mychips.chits for each row execute procedure mychips.chits_tf_notice();
create trigger mychips_tallies_tr_notice after update on mychips.tallies for each row execute procedure mychips.tallies_tf_notice();

--Data Dictionary:
insert into wm.table_text (tt_sch,tt_tab,language,title,help) values
  ('wm','releases','en','Releases','Tracks the version number of each public release of the database design'),
  ('wm','objects','en','Objects','Keeps data on database tables, views, functions, etc. telling how to build or drop each object and how it relates to other objects in the database.'),
  ('wm','objects_v','en','Rel Objects','An enhanced view of the object table, expanded by showing the full object specifier, and each separate release this version of the object belongs to'),
  ('wm','objects_v_depth','en','Dep Objects','An enhanced view of the object table, expanded by showing the full object specifier, each separate release this version of the object belongs to, and the maximum depth it is along any path in the dependency tree.'),
  ('wm','depends_v','en','Dependencies','A recursive view showing which database objects depend on (must be created after) other database objects.'),
  ('wm','table_style','en','Table Styles','Contains style flags to tell the GUI how to render each table or view'),
  ('wm','column_style','en','Column Styles','Contains style flags to tell the GUI how to render the columns of a table or view'),
  ('wm','table_text','en','Table Text','Contains a description of each table in the system'),
  ('wm','column_text','en','Column Text','Contains a description for each column of each table in the system'),
  ('wm','value_text','en','Value Text','Contains a description for the values which certain columns may be set to.  Used only for columns that can be set to one of a finite set of values (like an enumerated type).'),
  ('wm','message_text','en','Message Text','Contains messages in a particular language to describe an error, or a widget feature or button'),
  ('wm','column_native','en','Native Columns','Contains cached information about the tables and their columns which various higher level view columns derive from.  To query this directly from the information schema is somewhat slow, so wyseman caches it here when building the schema for faster access.'),
  ('wm','table_data','en','Table Data','Contains information from the system catalogs about views and tables in the system'),
  ('wm','table_pub','en','Tables','Joins information about tables from the system catalogs with the text descriptions defined in wyseman'),
  ('wm','view_column_usage','en','View Column Usage','A version of a similar view in the information schema but faster.  For each view, tells what underlying table and column the view column uses.'),
  ('wm','column_data','en','Column Data','Contains information from the system catalogs about columns of tables in the system'),
  ('wm','column_pub','en','Columns','Joins information about table columns from the system catalogs with the text descriptions defined in wyseman'),
  ('wm','fkeys_data','en','Keys Data','Includes data from the system catalogs about how key fields in a table point to key fields in a foreign table.  Each key group is described on a separate row.'),
  ('wm','fkeys_pub','en','Keys','Public view to see foreign key relationships between views and tables and what their native underlying tables/columns are.  One row per key group.'),
  ('wm','fkey_data','en','Key Data','Includes data from the system catalogs about how key fields in a table point to key fields in a foreign table.  Each separate key field is listed as a separate row.'),
  ('wm','fkey_pub','en','Key Info','Public view to see foreign key relationships between views and tables and what their native underlying tables/columns are.  One row per key column.'),
  ('wm','role_members','en','Role Members','Summarizes information from the system catalogs about members of various defined roles'),
  ('wm','column_ambig','en','Ambiguous Columns','A view showing view and their columns for which no definitive native table and column can be found automatically'),
  ('wylib','data','en','GUI Data','Configuration and preferences data accessed by Wylib view widgets'),
  ('wylib','data','fi','GUI Data','Wylib-näkymäkomponenttien käyttämät konfigurointi- ja asetustiedot'),
  ('base','addr','en','Addresses','Addresses (home, mailing, etc.) pertaining to entities'),
  ('base','addr_v','en','Addresses','A view of addresses (home, mailing, etc.) pertaining to entities, with additional derived fields'),
  ('base','addr_prim','en','Primary Address','Internal table to track which address is the main one for each given type'),
  ('base','comm','en','Communication','Communication points (phone, email, fax, etc.) for entities'),
  ('base','comm_v','en','Communication','View of users'' communication points (phone, email, fax, etc.) with additional helpful fields'),
  ('base','comm_prim','en','Primary Communication','Internal table to track which communication point is the main one for each given type'),
  ('base','country','en','Countries','Contains standard ISO data about international countries'),
  ('base','ent','en','Entities','Entities, which can be a person, a company or a group'),
  ('base','ent_v','en','Entities','A view of Entities, which can be a person, a company or a group, plus additional derived fields'),
  ('base','ent_link','en','Entity Links','Links to show how one entity (like an employee) is linked to another (like his company)'),
  ('base','ent_link_v','en','Entity Links','A view showing links to show how one entity (like an employee) is linked to another (like his company), plus the derived names of the entities'),
  ('base','parm','en','System Parameters','Contains parameter settings of several types for configuring and controlling various modules across the database'),
  ('base','parm_v','en','Parameters','System parameters are stored in different tables depending on their data type (date, integer, etc.).  This view is a union of all the different type tables so all parameters can be viewed and updated in one place.  The value specified will have to be entered in a way that is compatible with the specified type so it can be stored natively in its correct data type.'),
  ('base','priv','en','Privileges','Privileges assigned to each system user'),
  ('base','priv_v','en','Privileges','Privileges assigned to each entity'),
  ('public','covenants','en','Covenants','Each record contains contract language to be included by reference in a MyCHIPs tally or a similar agreement.'),
  ('mychips','peers','en','CHIP Peers','All entities who trade CHIPs using on this server.  Includes this server''s users and their peers.'),
  ('mychips','peers_v','en','CHIP Peers','Entities who trade CHIPs on this server, and their peer entities.'),
  ('mychips','tallies','en','Tallies','Contains an entry for each tally, which is a record of credit transactions between two trading partners.'),
  ('mychips','tallies_v','en','Tallies','Standard view containing an entry for each tally, which is a record of credit transactions between two trading partners.'),
  ('mychips','chits','en','Chits','Contains an entry for each transaction of credit flow in either direction between the parties to the tally.'),
  ('mychips','confirms','en','Confirmations','Contains records evidencing each time the parties confirmed the present balance of their tally.'),
  ('mychips','users','en','CHIP Users','Entities who have CHIP accounts on this server.'),
  ('mychips','users_v','en','CHIP Users','Entities who have CHIP accounts on this server.'),
  ('mychips','users','fi','CHIP käyttäjät','Yksiköt, joilla on CHIP-tilejä tällä palvelimella'),
  ('mychips','users_v','fi','CHIP käytäjät näkymä','Yksiköt, joilla on CHIP-tilejä tällä palvelimella');

insert into wm.column_text (ct_sch,ct_tab,ct_col,language,title,help) values
  ('wm','releases','release','en','Release','The integer number of the release, starting with 1.  The current number in this field always designates a work-in-progress.  The number prior indicates the last public release.'),
  ('wm','releases','crt_date','en','Created','When this record was created.  Indicates when development started on this release (And the prior release was frozen).'),
  ('wm','releases','sver_1','en','BS Version','Dummy column with a name indicating the version of these bootstrap tables (which can''t be managed by wyseman themselves).'),
  ('wm','objects','obj_typ','en','Type','The object type, for example: table, function, trigger, etc.'),
  ('wm','objects','obj_nam','en','Name','The schema and name of object as known within that schema'),
  ('wm','objects','obj_ver','en','Version','A sequential integer showing how many times this object has been modified, as a part of an official release.  Changes to the current (working) release do not increment this number.'),
  ('wm','objects','checked','en','Checked','This record has had its dependencies and consistency checked'),
  ('wm','objects','clean','en','Clean','The object represented by this record is built and current according to this create script'),
  ('wm','objects','module','en','Module','The name of a code module (package) this object belongs to'),
  ('wm','objects','mod_ver','en','Mod Vers','The version of the code module, or package this object belongs to'),
  ('wm','objects','source','en','Source','The basename of the external source code file this object was parsed from'),
  ('wm','objects','deps','en','Depends','A list of un-expanded dependencies for this object, exactly as expressed in the source file'),
  ('wm','objects','ndeps','en','Normal Deps','An expanded and normalized array of dependencies, guaranteed to exist in another record of the table'),
  ('wm','objects','grants','en','Grants','The permission grants found, applicable to this object'),
  ('wm','objects','col_data','en','Display','Switches found, expressing preferred display characteristics for columns, assuming this is a view or table object'),
  ('wm','objects','crt_sql','en','Create','The SQL code to build this object'),
  ('wm','objects','drp_sql','en','Drop','The SQL code to drop this object'),
  ('wm','objects','min_rel','en','Minimum','The oldest release this version of this object belongs to'),
  ('wm','objects','max_rel','en','Maximum','The latest release this version of this object belongs to'),
  ('wm','objects','crt_date','en','Created','When this object record was first created'),
  ('wm','objects','mod_date','en','Modified','When this object record was last modified'),
  ('wm','objects_v','object','en','Object','Full type and name of this object'),
  ('wm','objects_v','release','en','Release','A release this version of the object belongs to'),
  ('wm','objects_v_depth','depth','en','Max Depth','The maximum depth of this object along any path in the dependency tree'),
  ('wm','depends_v','object','en','Object','Full object type and name (type:name)'),
  ('wm','depends_v','obj_typ','en','Type','Function, view, table, etc'),
  ('wm','depends_v','obj_nam','en','Name','Schema and name of object as known within that schema'),
  ('wm','depends_v','depend','en','Depends On','Another object that must be created before this object'),
  ('wm','depends_v','release','en','Release','The release this object belongs to'),
  ('wm','depends_v','depth','en','Depth','The depth of the dependency tree, when following this particular dependency back to the root.'),
  ('wm','depends_v','path','en','Path','The path of the dependency tree above this object'),
  ('wm','depends_v','fpath','en','Full Path','The full path of the dependency tree above this object (including this object).'),
  ('wm','table_style','ts_sch','en','Schema Name','The schema for the table this style pertains to'),
  ('wm','table_style','ts_tab','en','Table Name','The name of the table this style pertains to'),
  ('wm','table_style','sw_name','en','Name','The name of the style being described'),
  ('wm','table_style','sw_value','en','Value','The value for this particular style'),
  ('wm','column_style','cs_sch','en','Schema Name','The schema for the table this style pertains to'),
  ('wm','column_style','cs_tab','en','Table Name','The name of the table containing the column this style pertains to'),
  ('wm','column_style','cs_col','en','Column Name','The name of the column this style pertains to'),
  ('wm','column_style','sw_name','en','Name','The name of the style being described'),
  ('wm','column_style','sw_value','en','Value','The value for this particular style'),
  ('wm','table_text','tt_sch','en','Schema Name','The schema this table belongs to'),
  ('wm','table_text','tt_tab','en','Table Name','The name of the table being described'),
  ('wm','table_text','language','en','Language','The language this description is in'),
  ('wm','table_text','title','en','Title','A short title for the table'),
  ('wm','table_text','help','en','Description','A longer description of what the table is used for'),
  ('wm','column_text','ct_sch','en','Schema Name','The schema this column''s table belongs to'),
  ('wm','column_text','ct_tab','en','Table Name','The name of the table this column is in'),
  ('wm','column_text','ct_col','en','Column Name','The name of the column being described'),
  ('wm','column_text','language','en','Language','The language this description is in'),
  ('wm','column_text','title','en','Title','A short title for the column'),
  ('wm','column_text','help','en','Description','A longer description of what the column is used for'),
  ('wm','value_text','vt_sch','en','Schema Name','The schema of the table the column belongs to'),
  ('wm','value_text','vt_tab','en','Table Name','The name of the table this column is in'),
  ('wm','value_text','vt_col','en','Column Name','The name of the column whose values are being described'),
  ('wm','value_text','value','en','Value','The name of the value being described'),
  ('wm','value_text','language','en','Language','The language this description is in'),
  ('wm','value_text','title','en','Title','A short title for the value'),
  ('wm','value_text','help','en','Description','A longer description of what it means when the column is set to this value'),
  ('wm','message_text','mt_sch','en','Schema Name','The schema of the table this message belongs to'),
  ('wm','message_text','mt_tab','en','Table Name','The name of the table this message belongs to is in'),
  ('wm','message_text','code','en','Code','A unique code referenced in the source code to evoke this message in the language of choice'),
  ('wm','message_text','language','en','Language','The language this message is in'),
  ('wm','message_text','title','en','Title','A short version for the message, or its alert'),
  ('wm','message_text','help','en','Description','A longer, more descriptive version of the message'),
  ('wm','column_native','cnt_sch','en','Schema Name','The schema of the table this column belongs to'),
  ('wm','column_native','cnt_tab','en','Table Name','The name of the table this column is in'),
  ('wm','column_native','cnt_col','en','Column Name','The name of the column whose native source is being described'),
  ('wm','column_native','nat_sch','en','Schema Name','The schema of the native table the column derives from'),
  ('wm','column_native','nat_tab','en','Table Name','The name of the table the column natively derives from'),
  ('wm','column_native','nat_col','en','Column Name','The name of the column in the native table from which the higher level column derives'),
  ('wm','column_native','nat_exp','en','Explic Native','The information about the native table in this record has been defined explicitly in the schema description (not derived from the database system catalogs)'),
  ('wm','column_native','pkey','en','Primary Key','Wyseman can often determine the "primary key" for views on its own from the database.  When it can''t, you have to define it explicitly in the schema.  This indicates that thiscolumn should be regarded as a primary key field when querying the view.'),
  ('wm','table_data','td_sch','en','Schema Name','The schema the table is in'),
  ('wm','table_data','td_tab','en','Table Name','The name of the table being described'),
  ('wm','table_data','tab_kind','en','Kind','Tells whether the relation is a table or a view'),
  ('wm','table_data','has_pkey','en','Has Pkey','Indicates whether the table has a primary key defined in the database'),
  ('wm','table_data','columns','en','Columns','Indicates how many columns are in the table'),
  ('wm','table_pub','sch','en','Schema Name','The schema the table belongs to'),
  ('wm','table_pub','tab','en','Table Name','The name of the table being described'),
  ('wm','table_pub','obj','en','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','view_column_usage','view_schema','en','View Schema','The schema the view belongs to'),
  ('wm','view_column_usage','view_name','en','View Name','The name of the view being described'),
  ('wm','view_column_usage','table_schema','en','Table Schema','The schema the underlying table belongs to'),
  ('wm','view_column_usage','table_name','en','Table Name','The name of the underlying table'),
  ('wm','view_column_usage','column_name','en','Column Name','The name of the column in the view'),
  ('wm','column_data','cdt_sch','en','Schema Name','The schema of the table this column belongs to'),
  ('wm','column_data','cdt_tab','en','Table Name','The name of the table this column is in'),
  ('wm','column_data','cdt_col','en','Column Name','The name of the column whose data is being described'),
  ('wm','column_data','field','en','Field','The number of the column as it appears in the table'),
  ('wm','column_data','nonull','en','Not Null','Indicates that the column is not allowed to contain a null value'),
  ('wm','column_data','is_pkey','en','Def Prim Key','Indicates that this column is defined as a primary key in the database (can be overridden by a wyseman setting)'),
  ('wm','column_pub','sch','en','Schema Name','The schema of the table the column belongs to'),
  ('wm','column_pub','tab','en','Table Name','The name of the table that holds the column being described'),
  ('wm','column_pub','col','en','Column Name','The name of the column being described'),
  ('wm','column_pub','obj','en','Object Name','The table name, prefixed by the schema (namespace) name'),
  ('wm','column_pub','nat','en','Native Object','The name of the native table, prefixed by the native schema'),
  ('wm','column_pub','language','en','Language','The language of the included textual descriptions'),
  ('wm','column_pub','title','en','Title','A short title for the table'),
  ('wm','column_pub','help','en','Description','A longer description of what the table is used for'),
  ('wm','fkeys_data','kst_sch','en','Base Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkeys_data','kst_tab','en','Base Table','The name of the table that has the referencing key fields'),
  ('wm','fkeys_data','kst_cols','en','Base Columns','The name of the columns in the referencing table''s key'),
  ('wm','fkeys_data','ksf_sch','en','Foreign Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkeys_data','ksf_tab','en','Foreign Table','The name of the table that is referenced by the key fields'),
  ('wm','fkeys_data','ksf_cols','en','Foreign Columns','The name of the columns in the referenced table''s key'),
  ('wm','fkeys_data','conname','en','Constraint','The name of the the foreign key constraint in the database'),
  ('wm','fkeys_pub','tt_sch','en','Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_tab','en','Table','The name of the table that has the referencing key fields'),
  ('wm','fkeys_pub','tt_cols','en','Columns','The name of the columns in the referencing table''s key'),
  ('wm','fkeys_pub','tt_obj','en','Object','Concatenated schema.table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_sch','en','Nat Schema','The schema of the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_tab','en','Nat Table','The name of the native table that has the referencing key fields'),
  ('wm','fkeys_pub','tn_cols','en','Nat Columns','The name of the columns in the native referencing table''s key'),
  ('wm','fkeys_pub','tn_obj','en','Nat Object','Concatenated schema.table for the native table that has the referencing key fields'),
  ('wm','fkeys_pub','ft_sch','en','For Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_tab','en','For Table','The name of the table that is referenced by the key fields'),
  ('wm','fkeys_pub','ft_cols','en','For Columns','The name of the columns referenced by the key'),
  ('wm','fkeys_pub','ft_obj','en','For Object','Concatenated schema.table for the table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_sch','en','For Nat Schema','The schema of the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_tab','en','For Nat Table','The name of the native table that is referenced by the key fields'),
  ('wm','fkeys_pub','fn_cols','en','For Nat Columns','The name of the columns in the native referenced by the key'),
  ('wm','fkeys_pub','fn_obj','en','For Nat Object','Concatenated schema.table for the native table that is referenced by the key fields'),
  ('wm','fkey_data','kyt_sch','en','Base Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkey_data','kyt_tab','en','Base Table','The name of the table that has the referencing key fields'),
  ('wm','fkey_data','kyt_col','en','Base Columns','The name of the column in the referencing table''s key'),
  ('wm','fkey_data','kyt_field','en','Base Field','The number of the column in the referencing table''s key'),
  ('wm','fkey_data','kyf_sch','en','Foreign Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkey_data','kyf_tab','en','Foreign Table','The name of the table that is referenced by the key fields'),
  ('wm','fkey_data','kyf_col','en','Foreign Columns','The name of the columns in the referenced table''s key'),
  ('wm','fkey_data','kyf_field','en','Foreign Field','The number of the column in the referenced table''s key'),
  ('wm','fkey_data','key','en','Key','The number of which field of a compound key this record describes'),
  ('wm','fkey_data','keys','en','Keys','The total number of columns used for this foreign key'),
  ('wm','fkey_data','conname','en','Constraint','The name of the the foreign key constraint in the database'),
  ('wm','fkey_pub','tt_sch','en','Schema','The schema of the table that has the referencing key fields'),
  ('wm','fkey_pub','tt_tab','en','Table','The name of the table that has the referencing key fields'),
  ('wm','fkey_pub','tt_col','en','Column','The name of the column in the referencing table''s key component'),
  ('wm','fkey_pub','tt_obj','en','Object','Concatenated schema.table that has the referencing key fields'),
  ('wm','fkey_pub','tn_sch','en','Nat Schema','The schema of the native table that has the referencing key fields'),
  ('wm','fkey_pub','tn_tab','en','Nat Table','The name of the native table that has the referencing key fields'),
  ('wm','fkey_pub','tn_col','en','Nat Column','The name of the column in the native referencing table''s key component'),
  ('wm','fkey_pub','tn_obj','en','Nat Object','Concatenated schema.table for the native table that has the referencing key fields'),
  ('wm','fkey_pub','ft_sch','en','For Schema','The schema of the table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_tab','en','For Table','The name of the table that is referenced by the key fields'),
  ('wm','fkey_pub','ft_col','en','For Column','The name of the column referenced by the key component'),
  ('wm','fkey_pub','ft_obj','en','For Object','Concatenated schema.table for the table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_sch','en','For Nat Schema','The schema of the native table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_tab','en','For Nat Table','The name of the native table that is referenced by the key fields'),
  ('wm','fkey_pub','fn_col','en','For Nat Column','The name of the column in the native referenced by the key component'),
  ('wm','fkey_pub','fn_obj','en','For Nat Object','Concatenated schema.table for the native table that is referenced by the key fields'),
  ('wm','fkey_pub','unikey','en','Unikey','Used to differentiate between multiple fkeys pointing to the same destination, and multi-field fkeys pointing to multi-field destinations'),
  ('wm','role_members','role','en','Role','The name of a role'),
  ('wm','role_members','member','en','Member','The username of a member of the named role'),
  ('wm','column_ambig','sch','en','Schema','The name of the schema this view is in'),
  ('wm','column_ambig','tab','en','Table','The name of the view'),
  ('wm','column_ambig','col','en','Column','The name of the column within the view'),
  ('wm','column_ambig','spec','en','Specified','True if the definitive native table has been specified explicitly in the schema definition files'),
  ('wm','column_ambig','count','en','Count','The number of possible native tables for this column'),
  ('wm','column_ambig','natives','en','Natives','A list of the possible native tables for this column'),
  ('wylib','data','ruid','en','Record ID','A unique ID number generated for each data record'),
  ('wylib','data','component','en','GUI Component','The part of the graphical interface that accesses this data'),
  ('wylib','data','access','en','Access','Who is allowed to access this data, and how'),
  ('wylib','data','owner','en','Owner','The user entity who created and has full permission to the data in this record'),
  ('wylib','data','data','en','JSON Data','A record in JSON (JavaScript Object Notation) in a format known and controlled by the view or other accessing module'),
  ('wylib','data','ruid','fi','Tunnistaa','Kullekin datatietueelle tuotettu yksilöllinen ID-numero'),
  ('wylib','data','component','fi','Komponentti','GUI:n osa joka käyttää tämä data'),
  ('wylib','data','access','fi','Pääsy','Kuka saa käyttää näitä tietoja ja miten'),
  ('base','addr','addr_ent','en','Entity ID','The ID number of the entity this address applies to'),
  ('base','addr','addr_seq','en','Sequence','A unique number assigned to each new address for a given entity'),
  ('base','addr','addr_spec','en','Address','Street address or PO Box.  This can occupy multiple lines if necessary'),
  ('base','addr','addr_type','en','Type','The kind of address'),
  ('base','addr','addr_prim','en','Primary','If checked this is the primary address for contacting this entity'),
  ('base','addr','addr_cmt','en','Comment','Any other notes about this address'),
  ('base','addr','city','en','City','The name of the city this address is in'),
  ('base','addr','state','en','State','The name of the state or province this address is in'),
  ('base','addr','pcode','en','Zip/Postal','Zip or other mailing code applicable to this address.'),
  ('base','addr','country','en','Country','The name of the country this address is in.  Use standard international country code abbreviations.'),
  ('base','addr','addr_inact','en','Inactive','If checked this address is no longer a valid address'),
  ('base','addr','dirty','en','Dirty','A flag used in the database backend to track whether the primary address needs to be recalculated'),
  ('base','addr','crt_date','en','Created','The date this record was created'),
  ('base','addr','crt_by','en','Created By','The user who entered this record'),
  ('base','addr','mod_date','en','Modified','The date this record was last modified'),
  ('base','addr','mod_by','en','Modified By','The user who last modified this record'),
  ('base','addr_v','std_name','en','entity Name','The name of the entity this address pertains to'),
  ('base','addr_prim','prim_ent','en','Entity','The entity ID number of the main address'),
  ('base','addr_prim','prim_seq','en','Sequence','The sequence number of the main address'),
  ('base','addr_prim','prim_spec','en','Medium','The address type this record applies to'),
  ('base','comm','comm_ent','en','Entity','The ID number of the entity this communication point belongs to'),
  ('base','comm','comm_seq','en','Sequence','A unique number assigned to each new address for a given entity'),
  ('base','comm','comm_spec','en','Num/Addr','The number or address to use when communication via this method and communication point'),
  ('base','comm','comm_type','en','Medium','The method of communication'),
  ('base','comm','comm_prim','en','Primary','If checked this is the primary method of this type for contacting this entity'),
  ('base','comm','comm_cmt','en','Comment','Any other notes about this communication point'),
  ('base','comm','comm_inact','en','Inactive','This box is checked to indicate that this record is no longer current'),
  ('base','comm','crt_date','en','Created','The date this record was created'),
  ('base','comm','crt_by','en','Created By','The user who entered this record'),
  ('base','comm','mod_date','en','Modified','The date this record was last modified'),
  ('base','comm','mod_by','en','Modified By','The user who last modified this record'),
  ('base','comm_v','std_name','en','Entity Name','The name of the entity this communication point pertains to'),
  ('base','comm_prim','prim_ent','en','Entity','The entity ID number of the main communication point'),
  ('base','comm_prim','prim_seq','en','Sequence','The sequence number of the main communication point'),
  ('base','comm_prim','prim_spec','en','Medium','The communication type this record applies to'),
  ('base','country','code','en','Country Code','The ISO 2-letter country code.  This is the offical value to use when entering countries in wylib applications.'),
  ('base','country','com_name','en','Country','The common name of the country in English'),
  ('base','country','capital','en','Capital','The name of the capital city'),
  ('base','country','cur_code','en','Currency','The standard code for the currency of this country'),
  ('base','country','cur_name','en','Curr Name','The common name in English of the currency of this country'),
  ('base','country','dial_code','en','Dial Code','The numeric code to dial when calling this country on the phone'),
  ('base','country','iso_3','en','Code 3','The ISO 3-letter code for this country (not the wylib standard)'),
  ('base','country','iana','en','Root Domain','The standard extension for WWW domain names for this country'),
  ('base','ent','id','en','Entity ID','A unique number assigned to each entity'),
  ('base','ent','ent_type','en','Entity Type','The kind of entity this record represents'),
  ('base','ent','ent_cmt','en','Ent Comment','Any other notes relating to this entity'),
  ('base','ent','ent_name','en','Entity Name','Company name, personal surname, or group name'),
  ('base','ent','fir_name','en','First Name','First given (Robert, Susan, William etc.) for person entities only'),
  ('base','ent','mid_name','en','Middle Names','One or more middle given or maiden names, for person entities only'),
  ('base','ent','pref_name','en','Preferred','Preferred first name (Bob, Sue, Bill etc.) for person entities only'),
  ('base','ent','title','en','Title','A title that prefixes the name (Mr., Chief, Dr. etc.)'),
  ('base','ent','born_date','en','Born Date','Birth date for person entities or optionally, an incorporation date for entities'),
  ('base','ent','gender','en','Gender','Whether the person is male (m) or female (f)'),
  ('base','ent','marital','en','Marital Status','Whether the person is married (m) or single (s)'),
  ('base','ent','username','en','Username','The login name for this person, if a user on this system'),
  ('base','ent','database','en','Data Access','A flag indicating that this entity has access to the ERP database'),
  ('base','ent','ent_inact','en','Inactive','A flag indicating that this entity is no longer current, in business, or alive'),
  ('base','ent','inside','en','Inside','A flag indicating that this person is somehow associated with this site (user, member, employee, etc.).  Inside people will be given an ID number in a lower range than outside people and companies.'),
  ('base','ent','country','en','Country','The country of primary citizenship (for people) or legal organization (companies)'),
  ('base','ent','tax_id','en','TID/SSN','The number by which the country recognizes this person or company for taxation purposes'),
  ('base','ent','bank','en','Bank Routing','Bank routing information: bank_number<:.;,>account_number'),
  ('base','ent','proxy','en','Proxy','ID of another person authorized to act on behalf of this employee where necessary in certain administrative functions of the ERP (like budgetary approvals)'),
  ('base','ent','crt_date','en','Created','The date this record was created'),
  ('base','ent','crt_by','en','Created By','The user who entered this record'),
  ('base','ent','mod_date','en','Modified','The date this record was last modified'),
  ('base','ent','mod_by','en','Modified By','The user who last modified this record'),
  ('base','ent_v','std_name','en','Std Name','The standard format for the entity''s name or, for a person, a standard format: Last, Preferred'),
  ('base','ent_v','frm_name','en','Formal Name','A person''s full name in a formal format: Last, Title First Middle'),
  ('base','ent_v','cas_name','en','Casual Name','A person''s full name in a casual format: First Last'),
  ('base','ent_v','giv_name','en','Given Name','A person''s First given name'),
  ('base','ent_link','org','en','Organization ID','The ID of the organization entity that the member entity belongs to'),
  ('base','ent_link','mem','en','Member ID','The ID of the entity that is a member of the organization'),
  ('base','ent_link','role','en','Member Role','The function or job description of the member within the organization'),
  ('base','ent_link','supr_path','en','Super Chain','An ordered list of superiors from the top down for this member in this organization'),
  ('base','ent_link_v','org_name','en','Org Name','The name of the organization or group entity the member belongs to'),
  ('base','ent_link_v','mem_name','en','Member Name','The name of the person who belongs to the organization'),
  ('base','ent_link_v','role','en','Role','The job description or duty of the member with respect to the organization he belongs to'),
  ('base','parm','module','en','Module','The system or module within the ERP this setting is applicable to'),
  ('base','parm','parm','en','Name','The name of the parameter setting'),
  ('base','parm','cmt','en','Comment','Notes you may want to add about why the setting is set to a particular value'),
  ('base','parm','type','en','Data Type','Indicates the native data type of this paramter (and hence the particular underlying table it will be stored in.)'),
  ('base','parm','v_int','en','Integer Value','The parameter value in the case when the type is an integer'),
  ('base','parm','v_date','en','Date Value','The parameter value in the case when the type is a date'),
  ('base','parm','v_text','en','Text Value','The parameter value in the case when the type is a character string'),
  ('base','parm','v_float','en','Float Value','The parameter value in the case when the type is a real number'),
  ('base','parm','v_boolean','en','Boolean Value','The parameter value in the case when the type is a boolean (true/false) value'),
  ('base','parm','crt_date','en','Created','The date this record was created'),
  ('base','parm','crt_by','en','Created By','The user who entered this record'),
  ('base','parm','mod_date','en','Modified','The date this record was last modified'),
  ('base','parm','mod_by','en','Modified By','The user who last modified this record'),
  ('base','parm_v','value','en','Value','The value for the parameter setting, expressed as a string'),
  ('base','priv','grantee','en','Grantee','The user receiving the privilege'),
  ('base','priv','priv','en','Privilege','The name of the privilege being granted'),
  ('base','priv','level','en','Access','What level of access within this privilege (view,use,manage)'),
  ('base','priv','priv_level','en','Priv Level','Shows the name the privilege level will refer to in the database.  This is formed by joining the privilege name and the level with an underscore.'),
  ('base','priv','cmt','en','Comment','Comments about this privilege allocation to this user'),
  ('base','priv_v','std_name','en','Entity Name','The name of the entity being granted the privilege'),
  ('base','priv_v','priv_list','en','Priv List','In the case where the privilege refers to a group role, this shows which underlying privileges belong to that role.'),
  ('base','priv_v','username','en','Username','The username within the database for this entity'),
  ('public','covenants','author','en','Author','The name of the author, organization, or publisher of the covenant (such as GPL, FSF, MyCHIPs.org, etc.)'),
  ('public','covenants','title','en','Title','A short, descriptive title which will be shown as a section header when a contract is rendered.'),
  ('public','covenants','version','en','Version','The version number, starting at 1, of this covenant.'),
  ('public','covenants','language','en','Language','The standard ISO code for the language in which the covenant is expressed.'),
  ('public','covenants','released','en','Released','The date this version of the covenant was first published.'),
  ('public','covenants','content','en','Content','The actual contract text, describing what the parties are agreeing to.'),
  ('public','covenants','hash','en','Hash','A standardized hash of the covenant text which can be referenced by other contracts to prove what has been included.'),
  ('mychips','peers','peer_ent','en','Entity link','A link to the entities base table'),
  ('mychips','peers','peer_cdi','en','CHIPs ID','The user''s CHIPs Domain Identifier, or CDI'),
  ('mychips','peers','peer_hid','en','Covert ID','A substitute ID by which direct trading partners will refer to this user, when conversing with other peers'),
  ('mychips','peers','peer_pub','en','Peer Public Key','The peer''s public key, known to other trading partners'),
  ('mychips','peers','peer_inet','en','Peer Net Addr','The IP number where other CHIP servers can connect to do trades with this peer'),
  ('mychips','peers','peer_port','en','Peer Port','The port where other servers will connect'),
  ('mychips','peers','peer_cmt','en','Peer Comments','Administrative comments about this peer'),
  ('mychips','peers','crt_date','en','Created','The date this record was created'),
  ('mychips','peers','crt_by','en','Created By','The user who entered this record'),
  ('mychips','peers','mod_date','en','Modified','The date this record was last modified'),
  ('mychips','peers','mod_by','en','Modified By','The user who last modified this record'),
  ('mychips','peers_v','peer_sock','en','Peer Socket','The IP Number, and port where other servers can connect to trade with this peer.'),
  ('mychips','tallies','tally_ent','en','Tally Entity','The ID number of the entity or person this tally belongs to'),
  ('mychips','tallies','tally_seq','en','Tally Sequence','A unique number among all tallies owned by this entity'),
  ('mychips','tallies','tally_guid','en','Tally GUID','A globally unique identifier for this tally'),
  ('mychips','tallies','tally_type','en','Tally Type','Determines if this entity is typically the creditor (stock) or the debtor (foil) for this tally'),
  ('mychips','tallies','tally_date','en','Tally Date','The date and time this tally was initiated between the parties'),
  ('mychips','tallies','version','en','Version','A number indicating the format standard this tally adheres to'),
  ('mychips','tallies','partner','en','Partner Entity','The entity id number of the other party to this tally'),
  ('mychips','tallies','contract','en','Contract','The hash ID of the standard contract this tally is based upon.'),
  ('mychips','tallies','status','en','Status','Current state of the tally'),
  ('mychips','tallies','request','en','Request','Requested next state for the tally'),
  ('mychips','tallies','comment','en','Comment','Any notes the user might want to enter regarding this tally'),
  ('mychips','tallies','user_sig','en','User Signed','The digital signature of the entity this tally belongs to'),
  ('mychips','tallies','part_sig','en','Partner Signed','The digital signature of the other party to this tally'),
  ('mychips','tallies','cr_lim','en','Credit Limit','The maximum amount the stock entity will allow the foil entity to accumulate in credit at one time'),
  ('mychips','tallies','dr_lim','en','Debit Limit','The maximum balance the foil entity will allow the stock to accumulate in the opposite direction of normal credit flow'),
  ('mychips','tallies','total_c','en','Total','A cached total of all the chits on this tally, from the perspective of the tally''s owner'),
  ('mychips','tallies_v','state','en','State','A computed value indicating the state of progress as the tally goes through its lifecycle'),
  ('mychips','tallies_v','action','en','Action','Indicates this tally requires some kind of action on the part of the user, such as accepting, rejecting, confirming, etc.'),
  ('mychips','chits','chit_ent','en','Tally Entity','Entity ID of the owner of the tally this chit belongs to'),
  ('mychips','chits','chit_seq','en','Tally Sequence','Sequence number of the owner of the tally this chit belongs to'),
  ('mychips','chits','chit_idx','en','Chit Index','A unique identifier within the tally, identifying this chit'),
  ('mychips','chits','chit_guid','en','Chit GUID','A globally unique identifier for this transaction'),
  ('mychips','chits','chit_type','en','Chit Type','The type of transaction represented by this flow of credit'),
  ('mychips','chits','chit_date','en','Date/Time','The date and time when this transaction is effective'),
  ('mychips','chits','amount','en','Amount','The amount of the transaction, as measured in micro-CHIPs (1/1,000,000)'),
  ('mychips','chits','pro_quo','en','Quid Pro Quo','A reference to an invoice, a purchase order, a receipt or other document evidencing goods or services rendered, and a trading relationship between the parties'),
  ('mychips','chits','memo','en','Memo','Any other description or explanation for the transaction'),
  ('mychips','confirms','conf_ent','en','Confirm Entity','Entity ID of the owner of the tally this confirmation belongs to'),
  ('mychips','confirms','conf_seq','en','Confirm Sequence','Sequence number of the owner of the tally this confirmation belongs to'),
  ('mychips','confirms','conf_idx','en','Confirm Index','A unique identifier within the tally, identifying this confirmation'),
  ('mychips','confirms','conf_guid','en','Confirmation GUID','A globally unique identifier for this confirmation'),
  ('mychips','confirms','conf_date','en','Date & Time','The date and time when this account total is computed'),
  ('mychips','confirms','sum','en','Sum','The total of all transaction, or chits, on this tally as of the confirmation moment, and as measured in micro-CHIPs (1/1,000,000)'),
  ('mychips','confirms','signature','en','Signature','The digital signature of the other party, computed on a record containing the other (non-signature) fields in this table'),
  ('mychips','users','user_ent','en','Entity link','A link to the entities base table.'),
  ('mychips','users','user_inet','en','User Net Addr','The IP number where the users''s mobile application connects'),
  ('mychips','users','user_port','en','User Port','The port to which the user''s mobile device will connect'),
  ('mychips','users','user_stat','en','Trading Status','The current state of the user''s account for trading of CHIPs'),
  ('mychips','users','user_cmt','en','User Comments','Administrative comments about this user'),
  ('mychips','users','host_id','en','Host ID','A unique code identifying the controller server that processes peer traffic for this user'),
  ('mychips','users','crt_date','en','Created','The date this record was created'),
  ('mychips','users','crt_by','en','Created By','The user who entered this record'),
  ('mychips','users','mod_date','en','Modified','The date this record was last modified'),
  ('mychips','users','mod_by','en','Modified By','The user who last modified this record'),
  ('mychips','users_v','user_sock','en','User Socket','The IP Number, and port to which the user''s mobile device will connect'),
  ('mychips','users','user_ent','fi','Entiteettien linkki','Yhteys yhteisön peruspöytään'),
  ('mychips','users','user_stat','fi','Kaupan tila','CHIP-tilin kaupankäynnin tilille'),
  ('mychips','users_v','mobi_socket','fi','Käyttäjä pistorasia','IP-numero ja portti, johon käyttäjän mobiililaite yhdistää');

insert into wm.value_text (vt_sch,vt_tab,vt_col,value,language,title,help) values
  ('wylib','data','access','priv','en','Private','Only the owner of this data can read, write or delete it'),
  ('wylib','data','access','read','en','Public Read','The owner can read and write, all others can read, or see it'),
  ('wylib','data','access','write','en','Public Write','Anyone can read, write, or delete this data'),
  ('wylib','data','access','priv','fi','Yksityinen','Vain näiden tietojen omistaja voi lukea, kirjoittaa tai poistaa sen'),
  ('wylib','data','access','read','fi','Julkinen Lukea','Omistaja voi lukea ja kirjoittaa, kaikki muut voivat lukea tai nähdä sen'),
  ('wylib','data','access','write','fi','Julkinen Kirjoittaa','Jokainen voi lukea, kirjoittaa tai poistaa näitä tietoja'),
  ('base','addr','addr_type','phys','en','Physical','Where the entity has people living or working'),
  ('base','addr','addr_type','mail','en','Mailing','Where mail and correspondence is received'),
  ('base','addr','addr_type','ship','en','Shipping','Where materials are picked up or delivered'),
  ('base','addr','addr_type','bill','en','billing','Where invoices and other accounting information are sent'),
  ('base','comm','comm_type','phone','en','Phone','A way to contact the entity via telephone'),
  ('base','comm','comm_type','email','en','Email','A way to contact the entity via email'),
  ('base','comm','comm_type','cell','en','Cell','A way to contact the entity via cellular telephone'),
  ('base','comm','comm_type','fax','en','FAX','A way to contact the entity via faxsimile'),
  ('base','comm','comm_type','text','en','Text Message','A way to contact the entity via email to text messaging'),
  ('base','comm','comm_type','web','en','Web Address','A World Wide Web address URL for this entity'),
  ('base','comm','comm_type','pager','en','Pager','A way to contact the entity via a mobile pager'),
  ('base','comm','comm_type','other','en','Other','Some other contact method for the entity'),
  ('base','ent','ent_type','p','en','Person','The entity is an individual'),
  ('base','ent','ent_type','o','en','Organization','The entity is an organization (such as a company or partnership) which may employ or include members of individual people or other organizations'),
  ('base','ent','ent_type','g','en','Group','The entity is a group of people, companies, and/or other groups'),
  ('base','ent','ent_type','r','en','Role','The entity is a role or position that may not correspond to a particular person or company'),
  ('base','ent','gender','','en','N/A','Gender is not applicable (such as for organizations or groups)'),
  ('base','ent','gender','m','en','Male','The person is male'),
  ('base','ent','gender','f','en','Female','The person is female'),
  ('base','ent','marital','','en','N/A','Maritcal status is not applicable (such as for organizations or groups)'),
  ('base','ent','marital','m','en','Married','The person is in a current marriage'),
  ('base','ent','marital','s','en','Single','The person has never married or is divorced or is the survivor of a deceased spouse'),
  ('base','parm','type','int','en','Integer','The parameter can contain only values of integer type (... -2, -1, 0, 1, 2 ...'),
  ('base','parm','type','date','en','Date','The parameter can contain only date values'),
  ('base','parm','type','text','en','Text','The parameter can contain any text value'),
  ('base','parm','type','float','en','Float','The parameter can contain only values of floating point type (integer portion, decimal, fractional portion)'),
  ('base','parm','type','boolean','en','Boolean','The parameter can contain only the values of true or false'),
  ('base','priv','level','role','en','Group Role','The privilege is really a group name which contains other privileges and levels'),
  ('base','priv','level','limit','en','View Only','Limited access - Can see data but not change it'),
  ('base','priv','level','user','en','Normal Use','Normal access for the user of this function or module - Includes normal changing of data'),
  ('base','priv','level','super','en','Supervisor','Supervisory privilege - Typically includes the ability to undo or override normal user functions.  Also includes granting of view, user privileges to others.'),
  ('mychips','tallies','tally_type','stock','en','Stock','The entity this tally belongs to is typically the creditor on transactions'),
  ('mychips','tallies','tally_type','foil','en','Foil','The entity this tally belongs to is typically the debtor on transactions'),
  ('mychips','tallies','status','void','en','Void','The tally has been abandoned before being affirmed by both parties'),
  ('mychips','tallies','status','draft','en','Draft','The tally have been suggested by one party but not yet accepted by the other party'),
  ('mychips','tallies','status','open','en','Open','The tally is affirmed by both parties and can be used for trading chits'),
  ('mychips','tallies','status','close','en','Close','No further trading can occur on this tally'),
  ('mychips','tallies','request','void','en','Void','One party has requested to abandon the tally agreement'),
  ('mychips','tallies','request','draft','en','Draft','One party is requesting ???'),
  ('mychips','tallies','request','open','en','Open','One party is requesting to open a tally according to the specified terms'),
  ('mychips','tallies','request','close','en','Close','One party is requesting to disable further trading on this tally'),
  ('mychips','chits','chit_type','gift','en','Gift','The credit is given without any consideration.  Most compliance contracts would deem this unenforceable.'),
  ('mychips','chits','chit_type','lift','en','Credit Lift','The transaction is part of a credit lift, so multiple chits should exist with the same ID number, which all net to zero in their effect to the relevant entity'),
  ('mychips','chits','chit_type','loan','en','Loan','The credit is not given, but is advanced with the expectation of a later return.  Consideration would normally be a note of some kind.'),
  ('mychips','chits','chit_type','tran','en','Transaction','The credit is exchanged for goods or services.  There should be an invoice or receipt referenced evidencing due consideration in order to make this transaction enforceable.'),
  ('mychips','users','user_stat','act','en','Active','Good to conduct trades'),
  ('mychips','users','user_stat','lck','en','Lockdown','Account in emergency lockdown.  Do not conduct trades which result in a net loss of credit.'),
  ('mychips','users','user_stat','off','en','Offline','Account completely off line.  No trades possible.'),
  ('mychips','users','user_stat','act','fi','Aktiivinen','Hyvä käydä kauppaa'),
  ('mychips','users','user_stat','lck','fi','Lukittu','Tili hätätilanteessa. Älä harjoita kauppoja, jotka johtavat nettotappioon.'),
  ('mychips','users','user_stat','off','fi','Irrotettu','Tili kokonaan pois päältä. Kaupat eivät ole mahdollisia.');

insert into wm.message_text (mt_sch,mt_tab,code,language,title,help) values
  ('wylib','data','IAT','en','Invalid Access Type','Access type must be: priv, read, or write'),
  ('wylib','data','dbe','en','Edit','Insert, change and delete records from the database view'),
  ('wylib','data','dbeColMenu','en','Column','Operations you can perform on this column of the preview'),
  ('wylib','data','dbeMenu','en','Editing','A menu of functions for editing a database record'),
  ('wylib','data','dbeInsert','en','Add New','Insert a new record into the database table'),
  ('wylib','data','dbeUpdate','en','Update','Modify changed fields in the existing database record'),
  ('wylib','data','dbeDelete','en','Delete','Delete this database record (can not be un-done)'),
  ('wylib','data','dbeClear','en','Clear','Empty the editing fields, discontinue editing any database record that may have been loaded'),
  ('wylib','data','dbeLoadRec','en','Load Record','Load a specific record from the database by its primary key'),
  ('wylib','data','dbePrimary','en','Primary Key','The value that uniquely identifies the current record among all the rows in the database table'),
  ('wylib','data','dbeActions','en','Actions','Perform various commands pertaining to this particular view and record'),
  ('wylib','data','dbeSubords','en','Preview','Toggle the viewing of views and records which relate to the currently loaded record'),
  ('wylib','data','winMenu','en','Window Functions','A menu of functions for the display and operation of this window'),
  ('wylib','data','winPinned','en','Window Pinned','Keep this window open until it is explicitly closed'),
  ('wylib','data','winClose','en','Close Window','Close this window'),
  ('wylib','data','winSave','en','Save State','Save the layout and operating state of this window, and all its subordinate windows'),
  ('wylib','data','winRestore','en','Restore State','Restore a previously saved state'),
  ('wylib','data','winToTop','en','Move To Top','Make this window show above others of its peers'),
  ('wylib','data','winToBottom','en','Move To Bottom','Place this window behind others of its peers'),
  ('wylib','data','winMinimize','en','Minimize','Shrink window down to an icon by which it can be re-opened'),
  ('wylib','data','dbpMenu','en','Preview','A menu of functions for operating on the preview list below'),
  ('wylib','data','dbpReload','en','Reload','Reload the records specified in the previous load'),
  ('wylib','data','dbpLoad','en','Load Default','Load the records shown in this view, by default'),
  ('wylib','data','dbpLoadAll','en','Load All','Load all records from this table'),
  ('wylib','data','dbpDefault','en','Default Columns','Set all column display and order to the database default'),
  ('wylib','data','dbpFilter','en','Filter','Load records according to filter criteria'),
  ('wylib','data','dbpVisible','en','Visible','A menu of columns where you can decide which ones are visible in the preview'),
  ('wylib','data','dbpVisCheck','en','Visible','Check the box to make this column visible'),
  ('wylib','data','dbpColAuto','en','Auto Size','Adjust the width of this column to be optimal for its contents'),
  ('wylib','data','dbpColHide','en','Hide Column','Remove this column from the display'),
  ('wylib','data','dbpNext','en','Next Record','Move the selection down one line and execute (normally edit) that new line'),
  ('wylib','data','dbpPrev','en','Prior Record','Move the selection up one line and execute (normally edit) that new line'),
  ('wylib','data','X.dbpColSel','en','Visible Columns','Show or hide individual columns'),
  ('wylib','data','X.dbpFooter','en','Footer','Check the box to turn on column summaries, at the bottom'),
  ('wylib','data','dbs','en','Filter Search','Load records according to filter criteria'),
  ('wylib','data','dbsSearch','en','Query Search','Run the configured selection query, returning matching records'),
  ('wylib','data','dbsSave','en','Save Query','Save the current query for future use'),
  ('wylib','data','dbsRecall','en','Recall Query','Recall a named query which has been previously saved'),
  ('wylib','data','modOK','en','OK','Press this button to acknowledge you have seen the posted message'),
  ('wylib','data','modYes','en','OK','Press this button to acknowledge you wish to proceed with the current operation'),
  ('wylib','data','modCancel','en','Cancel','Press this button if you want to abandon the operation and not proceed'),
  ('wylib','data','modError','en','Error','Something went wrong'),
  ('wylib','data','modNotice','en','Notice','The message is a warning or advice for the user'),
  ('wylib','data','modConfirm','en','Confirm','The user is asked to confirm before proceeding, or cancel to abandon the operation'),
  ('wylib','data','modQuery','en','Query','The user is asked for certain input data, and a confirmation before proceeding'),
  ('wylib','data','23505','en','Key Violation','An operation would have resulted in multiple records having duplicated data, which is required to be unique'),
  ('wylib','data','subWindow','en','Subordinate View','Open a preview of records in another table that relate to the currently loaded record from this view'),
  ('wylib','data','X','en',null,null),
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
  ('base','addr','CCO','en','Country','The country must always be specified (and in standard form)'),
  ('base','addr','CPA','en','Primary','There must be at least one address checked as primary'),
  ('base','comm','CPC','en','Primary','There must be at least one communication point of each type checked as primary'),
  ('base','ent','CFN','en','First Name','A first name is required for personal entities'),
  ('base','ent','CMN','en','Middle Name','A middle name is prohibited for non-personal entities'),
  ('base','ent','CPN','en','Pref Name','A preferred name is prohibited for non-personal entities'),
  ('base','ent','CTI','en','Title','A preferred title is prohibited for non-personal entities'),
  ('base','ent','CGN','en','Gender','Gender must not be specified for non-personal entities'),
  ('base','ent','CMS','en','Marital','Marital status must not be specified for non-personal entities'),
  ('base','ent','CBD','en','Born Date','A born date is required for inside people'),
  ('base','ent','CPA','en','Prime Addr','A primary address must be active'),
  ('base','ent_link','NBP','en','Illegal Entity Org','A personal entity can not be an organization (and have member entities)'),
  ('base','ent_link','PBC','en','Illegal Entity Member','Only personal entities can belong to company entities'),
  ('base','priv','NUN','en','No username found','The specified user has no username--This probably means he has not been added as a database user'),
  ('base','priv','UAE','en','User already exists','The specified username was found to already exist as a user in the database'),
  ('base','priv','ENF','en','Employee not found','While adding a user, the specified ID was not found to belong to anyone in the empl database table'),
  ('base','priv','UAD','en','User doesn''t exist','While dropping a user, the specified username was not found to exist in the database'),
  ('base','priv','UNF','en','Username not found','While dropping a user, the specified username was not found to exist in the empl database'),
  ('mychips','users','ABC','en','Test 1','A test message 1'),
  ('mychips','users','BCD','en','Test 2','A test message 2'),
  ('mychips','users','DEF','en','Test 3','A test message 3'),
  ('mychips','users_v','ticket','en','User Ticket','Generate a temporary, one-time pass to allow a user to establish a secure connection with the server'),
  ('mychips','users','ABC','fi','Koetus 1','Ensimmäinen testiviesti'),
  ('mychips','users','BCD','fi','Koetus 2','Toinen testiviesti'),
  ('mychips','users','DEF','fi','Koetus 3','Kolmanen testiviesti');

insert into wm.table_style (ts_sch,ts_tab,sw_name,sw_value) values
  ('wm','table_text','focus','code'),
  ('wm','column_text','focus','code'),
  ('wm','value_text','focus','code'),
  ('wm','message_text','focus','code'),
  ('wm','column_pub','focus','code'),
  ('wm','objects','focus','obj_nam');

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
  ('wm','objects','obj_nam','focus','true');

insert into wm.column_native (cnt_sch,cnt_tab,cnt_col,nat_sch,nat_tab,nat_col,nat_exp,pkey) values
  ('base','country','cur_name','base','country','cur_name','f','f'),
  ('base','comm_v','comm_inact','base','comm','comm_inact','f','f'),
  ('base','comm','comm_inact','base','comm','comm_inact','f','f'),
  ('base','comm_v','mod_date','base','comm','mod_date','f','f'),
  ('mychips','users_v_flat','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','peers_v_flat','mod_date','mychips','peers','mod_date','f','f'),
  ('base','addr_v','mod_date','base','addr','mod_date','f','f'),
  ('wylib','data_v','mod_date','wylib','data','mod_date','f','f'),
  ('mychips','tokens_v','mod_date','mychips','tokens','mod_date','f','f'),
  ('base','parm_v','mod_date','base','parm','mod_date','f','f'),
  ('base','ent_v_pub','mod_date','base','ent','mod_date','f','f'),
  ('base','ent_link_v','mod_date','base','ent_link','mod_date','f','f'),
  ('wylib','data','mod_date','wylib','data','mod_date','f','f'),
  ('mychips','chits','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','tokens','mod_date','mychips','tokens','mod_date','f','f'),
  ('base','comm','mod_date','base','comm','mod_date','f','f'),
  ('mychips','users','mod_date','mychips','users','mod_date','f','f'),
  ('base','ent_v','mod_date','base','ent','mod_date','f','f'),
  ('mychips','peers','mod_date','mychips','peers','mod_date','f','f'),
  ('base','ent_link','mod_date','base','ent_link','mod_date','f','f'),
  ('mychips','tallies','mod_date','mychips','tallies','mod_date','f','f'),
  ('base','parm','mod_date','base','parm','mod_date','f','f'),
  ('base','addr','mod_date','base','addr','mod_date','f','f'),
  ('base','ent','mod_date','base','ent','mod_date','f','f'),
  ('wm','objects_v_depth','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects_v','mod_date','wm','objects','mod_date','f','f'),
  ('wm','objects','mod_date','wm','objects','mod_date','f','f'),
  ('mychips','users_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('mychips','peers_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('base','addr_v_flat','ship_state','base','addr_v_flat','ship_state','f','f'),
  ('mychips','users_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('mychips','peers_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('base','comm_v_flat','cell_comm','base','comm_v_flat','cell_comm','f','f'),
  ('mychips','chits','chit_type','mychips','chits','chit_type','f','f'),
  ('wm','depends_v','od_release','wm','depends_v','od_release','f','f'),
  ('mychips','users_v_flat','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','peers_v_flat','giv_name','base','ent_v','giv_name','f','f'),
  ('base','ent_v','giv_name','base','ent_v','giv_name','f','f'),
  ('wm','depends_v','od_typ','wm','depends_v','od_typ','f','f'),
  ('mychips','users_v_flat','database','base','ent','database','f','f'),
  ('mychips','peers_v_flat','database','base','ent','database','f','f'),
  ('base','priv_v','database','base','ent','database','f','f'),
  ('base','ent_v','database','base','ent','database','f','f'),
  ('base','ent','database','base','ent','database','f','f'),
  ('base','country','com_name','base','country','com_name','f','f'),
  ('wm','table_style','sw_value','wm','table_style','sw_value','f','f'),
  ('wm','column_style','sw_value','wm','column_style','sw_value','f','f'),
  ('base','country','cur_code','base','country','cur_code','f','f'),
  ('mychips','users_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('mychips','peers_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('base','addr_v_flat','ship_country','base','addr_v_flat','ship_country','f','f'),
  ('mychips','users_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('mychips','peers_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('base','addr_v_flat','bill_state','base','addr_v_flat','bill_state','f','f'),
  ('base','parm','v_int','base','parm','v_int','f','f'),
  ('base','parm_audit','a_reason','base','parm_audit','a_reason','f','f'),
  ('base','ent_audit','a_reason','base','ent_audit','a_reason','f','f'),
  ('wm','depends_v','depend','wm','depends_v','depend','f','f'),
  ('wm','depends_v','cycle','wm','depends_v','cycle','f','f'),
  ('wm','objects_v_depth','module','wm','objects','module','f','f'),
  ('wm','objects_v','module','wm','objects','module','f','f'),
  ('wm','objects','module','wm','objects','module','f','f'),
  ('mychips','tokens_v','allows','mychips','tokens','allows','f','f'),
  ('mychips','tokens','allows','mychips','tokens','allows','f','f'),
  ('wylib','data_v','component','wylib','data','component','f','f'),
  ('wylib','data','component','wylib','data','component','f','f'),
  ('mychips','users_v_flat','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v_flat','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','peers_v_flat','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','peers','peer_hid','mychips','peers','peer_hid','f','f'),
  ('base','ent_link_v','supr_path','base','ent_link','supr_path','f','f'),
  ('base','ent_link','supr_path','base','ent_link','supr_path','f','f'),
  ('wm','depends_v','od_nam','wm','depends_v','od_nam','f','f'),
  ('base','parm','v_date','base','parm','v_date','f','f'),
  ('wm','value_text','help','wm','value_text','help','f','f'),
  ('wm','table_text','help','wm','table_text','help','f','f'),
  ('wm','message_text','help','wm','message_text','help','f','f'),
  ('wm','column_text','help','wm','column_text','help','f','f'),
  ('base','addr_v','addr_type','base','addr','addr_type','f','f'),
  ('base','addr','addr_type','base','addr','addr_type','f','f'),
  ('mychips','users_v_flat','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','peers_v_flat','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','tokens_v','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','peers','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','users_v_flat','marital','base','ent','marital','f','f'),
  ('mychips','peers_v_flat','marital','base','ent','marital','f','f'),
  ('base','ent_v','marital','base','ent','marital','f','f'),
  ('base','ent','marital','base','ent','marital','f','f'),
  ('wm','objects_v_depth','object','wm','objects_v','object','f','f'),
  ('wm','objects_v','object','wm','objects_v','object','f','f'),
  ('wm','depends_v','object','wm','depends_v','object','f','f'),
  ('mychips','users_v_flat','peer_sock','mychips','users_v','peer_sock','f','f'),
  ('mychips','peers_v_flat','peer_sock','mychips','peers_v','peer_sock','f','f'),
  ('mychips','users_v_flat','ent_type','base','ent','ent_type','f','f'),
  ('mychips','peers_v_flat','ent_type','base','ent','ent_type','f','f'),
  ('base','ent_v_pub','ent_type','base','ent','ent_type','f','f'),
  ('base','ent_v','ent_type','base','ent','ent_type','f','f'),
  ('base','ent','ent_type','base','ent','ent_type','f','f'),
  ('wm','objects_v_depth','deps','wm','objects','deps','f','f'),
  ('wm','objects_v','deps','wm','objects','deps','f','f'),
  ('wm','objects','deps','wm','objects','deps','f','f'),
  ('base','ent_link_v','mem_name','base','ent_link_v','mem_name','f','f'),
  ('base','comm_v_flat','other_comm','base','comm_v_flat','other_comm','f','f'),
  ('base','parm_audit','a_by','base','parm_audit','a_by','f','f'),
  ('base','ent_audit','a_by','base','ent_audit','a_by','f','f'),
  ('mychips','comm_test','test_seq','mychips','comm_test','test_seq','f','f'),
  ('base','comm_v','comm_spec','base','comm','comm_spec','f','f'),
  ('base','comm','comm_spec','base','comm','comm_spec','f','f'),
  ('mychips','tokens_v','token_cmt','mychips','tokens','token_cmt','f','f'),
  ('base','priv_v','priv_list','base','priv_v','priv_list','f','f'),
  ('mychips','tokens','token_cmt','mychips','tokens','token_cmt','f','f'),
  ('mychips','tokens_v','valid','mychips','tokens_v','valid','f','f'),
  ('mychips','tallies','version','mychips','tallies','version','f','f'),
  ('base','comm_v','comm_type','base','comm','comm_type','f','f'),
  ('base','comm','comm_type','base','comm','comm_type','f','f'),
  ('mychips','users_v_flat','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','peers_v_flat','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent_v_pub','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent_v','ent_inact','base','ent','ent_inact','f','f'),
  ('base','ent','ent_inact','base','ent','ent_inact','f','f'),
  ('base','parm_v','value','base','parm_v','value','f','f'),
  ('mychips','chits','units','mychips','chits','units','f','f'),
  ('base','addr_v','state','base','addr','state','f','f'),
  ('base','addr','state','base','addr','state','f','f'),
  ('base','addr_v','city','base','addr','city','f','f'),
  ('base','addr','city','base','addr','city','f','f'),
  ('wm','objects_v_depth','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects_v','drp_sql','wm','objects','drp_sql','f','f'),
  ('wm','objects','drp_sql','wm','objects','drp_sql','f','f'),
  ('base','priv_v','level','base','priv','level','f','f'),
  ('base','priv','level','base','priv','level','f','f'),
  ('mychips','users_v_flat','country','base','ent','country','f','f'),
  ('mychips','peers_v_flat','country','base','ent','country','f','f'),
  ('base','addr_v','country','base','addr','country','f','f'),
  ('mychips','tokens_v','used','mychips','tokens','used','f','f'),
  ('mychips','tokens','used','mychips','tokens','used','f','f'),
  ('base','ent_v','country','base','ent','country','f','f'),
  ('base','addr','country','base','addr','country','f','f'),
  ('base','ent','country','base','ent','country','f','f'),
  ('mychips','tokens_v','exp_date','mychips','tokens','exp_date','f','f'),
  ('mychips','tokens','exp_date','mychips','tokens','exp_date','f','f'),
  ('mychips','users_v_flat','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','peers_v_flat','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','peers','peer_inet','mychips','peers','peer_inet','f','f'),
  ('base','comm_v_flat','pager_comm','base','comm_v_flat','pager_comm','f','f'),
  ('mychips','tallies','dr_limit','mychips','tallies','dr_limit','f','f'),
  ('mychips','users_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('mychips','peers_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('base','comm_v_flat','email_comm','base','comm_v_flat','email_comm','f','f'),
  ('mychips','users_v_flat','user_sock','mychips','users_v','user_sock','f','f'),
  ('mychips','covenants','content','mychips','covenants','content','f','f'),
  ('mychips','tallies','part_sig','mychips','tallies','part_sig','f','f'),
  ('base','parm','v_boolean','base','parm','v_boolean','f','f'),
  ('mychips','users_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('mychips','peers_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('base','addr_v_flat','bill_pcode','base','addr_v_flat','bill_pcode','f','f'),
  ('mychips','tallies','user_sig','mychips','tallies','user_sig','f','f'),
  ('wm','objects_v_depth','grants','wm','objects','grants','f','f'),
  ('wm','objects_v','grants','wm','objects','grants','f','f'),
  ('wm','objects','grants','wm','objects','grants','f','f'),
  ('mychips','users_v_flat','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','peers_v_flat','ent_cmt','base','ent','ent_cmt','f','f'),
  ('base','ent_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('base','ent','ent_cmt','base','ent','ent_cmt','f','f'),
  ('base','addr_v','pcode','base','addr','pcode','f','f'),
  ('base','addr','pcode','base','addr','pcode','f','f'),
  ('wm','objects_v_depth','mod_ver','wm','objects','mod_ver','f','f'),
  ('wm','objects_v','mod_ver','wm','objects','mod_ver','f','f'),
  ('wm','objects','mod_ver','wm','objects','mod_ver','f','f'),
  ('base','country','capital','base','country','capital','f','f'),
  ('mychips','tallies','contract','mychips','tallies','contract','f','f'),
  ('wylib','data_v','data','wylib','data','data','f','f'),
  ('wylib','data','data','wylib','data','data','f','f'),
  ('base','country','iso_3','base','country','iso_3','f','f'),
  ('mychips','users_v_flat','user_inet','mychips','users','user_inet','f','f'),
  ('mychips','tokens_v','user_inet','mychips','users','user_inet','f','f'),
  ('mychips','users','user_inet','mychips','users','user_inet','f','f'),
  ('wm','objects_v_depth','source','wm','objects','source','f','f'),
  ('wm','objects_v','source','wm','objects','source','f','f'),
  ('wm','objects','source','wm','objects','source','f','f'),
  ('mychips','users_v_flat','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','peers_v_flat','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','peers','peer_port','mychips','peers','peer_port','f','f'),
  ('base','comm_v','comm_prim','base','comm_v','comm_prim','f','f'),
  ('base','comm','comm_prim','base','comm','comm_prim','f','f'),
  ('base','priv_v','cmt','base','priv','cmt','f','f'),
  ('base','parm_v','cmt','base','parm','cmt','f','f'),
  ('base','priv','cmt','base','priv','cmt','f','f'),
  ('base','parm','cmt','base','parm','cmt','f','f'),
  ('wm','column_native','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_native','nat_sch','wm','column_native','nat_sch','f','f'),
  ('mychips','users_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('mychips','peers_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('base','addr_v_flat','bill_addr','base','addr_v_flat','bill_addr','f','f'),
  ('mychips','tallies','cr_limit','mychips','tallies','cr_limit','f','f'),
  ('mychips','users_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('mychips','peers_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('base','comm_v_flat','web_comm','base','comm_v_flat','web_comm','f','f'),
  ('mychips','users_v_flat','proxy','base','ent','proxy','f','f'),
  ('mychips','peers_v_flat','proxy','base','ent','proxy','f','f'),
  ('base','ent_v','proxy','base','ent','proxy','f','f'),
  ('base','ent','proxy','base','ent','proxy','f','f'),
  ('mychips','chits','chit_guid','mychips','chits','chit_guid','f','f'),
  ('base','parm_audit','a_date','base','parm_audit','a_date','f','f'),
  ('base','ent_audit','a_date','base','ent_audit','a_date','f','f'),
  ('base','parm','v_float','base','parm','v_float','f','f'),
  ('mychips','tallies','tally_date','mychips','tallies','tally_date','f','f'),
  ('base','comm_v','crt_date','base','comm','crt_date','f','f'),
  ('mychips','users_v_flat','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','peers_v_flat','crt_date','mychips','peers','crt_date','f','f'),
  ('base','addr_v','crt_date','base','addr','crt_date','f','f'),
  ('wylib','data_v','crt_date','wylib','data','crt_date','f','f'),
  ('mychips','tokens_v','crt_date','mychips','tokens','crt_date','f','f'),
  ('base','parm_v','crt_date','base','parm','crt_date','f','f'),
  ('base','ent_v_pub','crt_date','base','ent','crt_date','f','f'),
  ('base','ent_link_v','crt_date','base','ent_link','crt_date','f','f'),
  ('wylib','data','crt_date','wylib','data','crt_date','f','f'),
  ('mychips','chits','crt_date','mychips','chits','crt_date','f','f'),
  ('mychips','tokens','crt_date','mychips','tokens','crt_date','f','f'),
  ('base','comm','crt_date','base','comm','crt_date','f','f'),
  ('mychips','users','crt_date','mychips','users','crt_date','f','f'),
  ('base','ent_v','crt_date','base','ent','crt_date','f','f'),
  ('mychips','peers','crt_date','mychips','peers','crt_date','f','f'),
  ('base','ent_link','crt_date','base','ent_link','crt_date','f','f'),
  ('mychips','tallies','crt_date','mychips','tallies','crt_date','f','f'),
  ('base','parm','crt_date','base','parm','crt_date','f','f'),
  ('base','addr','crt_date','base','addr','crt_date','f','f'),
  ('base','ent','crt_date','base','ent','crt_date','f','f'),
  ('wm','objects_v_depth','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects_v','crt_date','wm','objects','crt_date','f','f'),
  ('wm','objects','crt_date','wm','objects','crt_date','f','f'),
  ('wm','releases','crt_date','wm','releases','crt_date','f','f'),
  ('mychips','users_v_flat','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','peers_v_flat','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','peers','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','tallies','status','mychips','tallies','status','f','f'),
  ('base','addr_v','addr_prim','base','addr_v','addr_prim','f','f'),
  ('base','addr','addr_prim','base','addr','addr_prim','f','f'),
  ('mychips','users_v_flat','ent_name','base','ent','ent_name','f','f'),
  ('mychips','peers_v_flat','ent_name','base','ent','ent_name','f','f'),
  ('base','ent_v','ent_name','base','ent','ent_name','f','f'),
  ('base','ent','ent_name','base','ent','ent_name','f','f'),
  ('mychips','confirms','conf_id','mychips','confirms','conf_id','f','f'),
  ('mychips','chits','request','mychips','chits','request','f','f'),
  ('mychips','tallies','request','mychips','tallies','request','f','f'),
  ('wm','column_native','nat_exp','wm','column_native','nat_exp','f','f'),
  ('base','parm_audit','a_column','base','parm_audit','a_column','f','f'),
  ('base','ent_audit','a_column','base','ent_audit','a_column','f','f'),
  ('mychips','users_v_flat','bank','base','ent','bank','f','f'),
  ('mychips','peers_v_flat','bank','base','ent','bank','f','f'),
  ('base','ent_v','bank','base','ent','bank','f','f'),
  ('base','ent','bank','base','ent','bank','f','f'),
  ('mychips','tallies','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tokens_v','token','mychips','tokens','token','f','f'),
  ('base','ent_link_v','org_name','base','ent_link_v','org_name','f','f'),
  ('mychips','tokens','token','mychips','tokens','token','f','f'),
  ('mychips','comm_test','test_ent','mychips','comm_test','test_ent','f','f'),
  ('mychips','confirms','signature','mychips','confirms','signature','f','f'),
  ('mychips','chits','signature','mychips','chits','signature','f','f'),
  ('base','parm_audit','a_value','base','parm_audit','a_value','f','f'),
  ('base','ent_audit','a_value','base','ent_audit','a_value','f','f'),
  ('mychips','confirms','sum','mychips','confirms','sum','f','f'),
  ('mychips','users_v_flat','fir_name','base','ent','fir_name','f','f'),
  ('mychips','peers_v_flat','fir_name','base','ent','fir_name','f','f'),
  ('base','ent_v','fir_name','base','ent','fir_name','f','f'),
  ('base','ent','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('mychips','peers_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('base','addr_v_flat','ship_pcode','base','addr_v_flat','ship_pcode','f','f'),
  ('wm','depends_v','fpath','wm','depends_v','fpath','f','f'),
  ('mychips','users_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('mychips','peers_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('base','addr_v_flat','bill_country','base','addr_v_flat','bill_country','f','f'),
  ('mychips','users_v_flat','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','peers_v_flat','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','peers','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','users_v_flat','title','base','ent','title','f','f'),
  ('mychips','peers_v_flat','title','base','ent','title','f','f'),
  ('base','ent_v','title','base','ent','title','f','f'),
  ('base','ent','title','base','ent','title','f','f'),
  ('wm','value_text','title','wm','value_text','title','f','f'),
  ('wm','table_text','title','wm','table_text','title','f','f'),
  ('wm','message_text','title','wm','message_text','title','f','f'),
  ('wm','column_text','title','wm','column_text','title','f','f'),
  ('wm','depends_v','path','wm','depends_v','path','f','f'),
  ('mychips','users_v_flat','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','peers_v_flat','frm_name','base','ent_v','frm_name','f','f'),
  ('base','ent_v','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','comm_test','test_dat','mychips','comm_test','test_dat','f','f'),
  ('wm','objects_v_depth','clean','wm','objects','clean','f','f'),
  ('wm','objects_v','clean','wm','objects','clean','f','f'),
  ('wm','objects','clean','wm','objects','clean','f','f'),
  ('mychips','covenants','hash','mychips','covenants','hash','f','f'),
  ('mychips','tallies','total_c','mychips','tallies','total_c','f','f'),
  ('wm','objects_v_depth','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects_v','ndeps','wm','objects','ndeps','f','f'),
  ('wm','objects','ndeps','wm','objects','ndeps','f','f'),
  ('mychips','tallies','comment','mychips','tallies','comment','f','f'),
  ('base','country','iana','base','country','iana','f','f'),
  ('wylib','data_v','access','wylib','data','access','f','f'),
  ('wylib','data','access','wylib','data','access','f','f'),
  ('wm','objects_v_depth','checked','wm','objects','checked','f','f'),
  ('wm','objects_v','checked','wm','objects','checked','f','f'),
  ('wm','objects','checked','wm','objects','checked','f','f'),
  ('base','parm','v_text','base','parm','v_text','f','f'),
  ('mychips','chits','pro_quo','mychips','chits','pro_quo','f','f'),
  ('wm','column_native','pkey','wm','column_native','pkey','f','f'),
  ('mychips','tallies','tally_guid','mychips','tallies','tally_guid','f','f'),
  ('base','comm_v','crt_by','base','comm','crt_by','f','f'),
  ('mychips','users_v_flat','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','peers_v_flat','crt_by','mychips','peers','crt_by','f','f'),
  ('base','addr_v','crt_by','base','addr','crt_by','f','f'),
  ('wylib','data_v','crt_by','wylib','data','crt_by','f','f'),
  ('mychips','tokens_v','crt_by','mychips','tokens','crt_by','f','f'),
  ('base','parm_v','crt_by','base','parm','crt_by','f','f'),
  ('base','ent_v_pub','crt_by','base','ent','crt_by','f','f'),
  ('base','ent_link_v','crt_by','base','ent_link','crt_by','f','f'),
  ('wylib','data','crt_by','wylib','data','crt_by','f','f'),
  ('mychips','chits','crt_by','mychips','chits','crt_by','f','f'),
  ('mychips','tokens','crt_by','mychips','tokens','crt_by','f','f'),
  ('base','comm','crt_by','base','comm','crt_by','f','f'),
  ('mychips','users','crt_by','mychips','users','crt_by','f','f'),
  ('base','ent_v','crt_by','base','ent','crt_by','f','f'),
  ('mychips','peers','crt_by','mychips','peers','crt_by','f','f'),
  ('base','ent_link','crt_by','base','ent_link','crt_by','f','f'),
  ('mychips','tallies','crt_by','mychips','tallies','crt_by','f','f'),
  ('base','parm','crt_by','base','parm','crt_by','f','f'),
  ('base','addr','crt_by','base','addr','crt_by','f','f'),
  ('base','ent','crt_by','base','ent','crt_by','f','f'),
  ('base','ent_link_v','role','base','ent_link','role','f','f'),
  ('base','ent_link','role','base','ent_link','role','f','f'),
  ('mychips','tokens_v','expired','mychips','tokens_v','expired','f','f'),
  ('base','comm_v','comm_cmt','base','comm','comm_cmt','f','f'),
  ('base','comm','comm_cmt','base','comm','comm_cmt','f','f'),
  ('base','comm_v_flat','fax_comm','base','comm_v_flat','fax_comm','f','f'),
  ('mychips','chits','memo','mychips','chits','memo','f','f'),
  ('mychips','users_v_flat','inside','base','ent','inside','f','f'),
  ('mychips','peers_v_flat','inside','base','ent','inside','f','f'),
  ('base','ent_v_pub','inside','base','ent','inside','f','f'),
  ('base','ent_v','inside','base','ent','inside','f','f'),
  ('base','ent','inside','base','ent','inside','f','f'),
  ('mychips','users_v_flat','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','peers_v_flat','cas_name','base','ent_v','cas_name','f','f'),
  ('base','ent_v','cas_name','base','ent_v','cas_name','f','f'),
  ('wm','objects_v_depth','col_data','wm','objects','col_data','f','f'),
  ('wm','objects_v','col_data','wm','objects','col_data','f','f'),
  ('wm','objects','col_data','wm','objects','col_data','f','f'),
  ('mychips','users_v_flat','user_port','mychips','users','user_port','f','f'),
  ('mychips','tokens_v','user_port','mychips','users','user_port','f','f'),
  ('mychips','users','user_port','mychips','users','user_port','f','f'),
  ('wm','column_native','nat_col','wm','column_native','nat_col','f','f'),
  ('mychips','users_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('mychips','peers_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('base','addr_v_flat','bill_city','base','addr_v_flat','bill_city','f','f'),
  ('wm','objects_v_depth','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects_v','max_rel','wm','objects','max_rel','f','f'),
  ('wm','objects','max_rel','wm','objects','max_rel','f','f'),
  ('mychips','covenants','released','mychips','covenants','released','f','f'),
  ('base','parm_v','type','base','parm','type','f','f'),
  ('base','parm','type','base','parm','type','f','f'),
  ('base','country','dial_code','base','country','dial_code','f','f'),
  ('mychips','users_v_flat','born_date','base','ent','born_date','f','f'),
  ('mychips','peers_v_flat','born_date','base','ent','born_date','f','f'),
  ('base','ent_v','born_date','base','ent','born_date','f','f'),
  ('base','ent','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('mychips','peers_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('base','addr_v_flat','ship_city','base','addr_v_flat','ship_city','f','f'),
  ('wm','objects_v_depth','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects_v','crt_sql','wm','objects','crt_sql','f','f'),
  ('wm','objects','crt_sql','wm','objects','crt_sql','f','f'),
  ('mychips','chits','chit_date','mychips','chits','chit_date','f','f'),
  ('wm','releases','sver_1','wm','releases','sver_1','f','f'),
  ('mychips','users_v_flat','username','base','ent','username','f','f'),
  ('mychips','users_v_flat','mid_name','base','ent','mid_name','f','f'),
  ('mychips','peers_v_flat','username','base','ent','username','f','f'),
  ('mychips','peers_v_flat','mid_name','base','ent','mid_name','f','f'),
  ('base','priv_v','username','base','ent','username','f','f'),
  ('base','ent_v_pub','username','base','ent','username','f','f'),
  ('base','ent_v','username','base','ent','username','f','f'),
  ('base','ent_v','mid_name','base','ent','mid_name','f','f'),
  ('base','ent','username','base','ent','username','f','f'),
  ('base','ent','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v_flat','pref_name','base','ent','pref_name','f','f'),
  ('mychips','peers_v_flat','pref_name','base','ent','pref_name','f','f'),
  ('base','ent_v','pref_name','base','ent','pref_name','f','f'),
  ('base','ent','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v_flat','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users','user_cmt','mychips','users','user_cmt','f','f'),
  ('base','comm_v_flat','text_comm','base','comm_v_flat','text_comm','f','f'),
  ('wm','objects_v_depth','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects_v','min_rel','wm','objects','min_rel','f','f'),
  ('wm','objects','min_rel','wm','objects','min_rel','f','f'),
  ('mychips','users_v_flat','host_id','mychips','users','host_id','f','f'),
  ('mychips','users','host_id','mychips','users','host_id','f','f'),
  ('mychips','users_v_flat','tax_id','base','ent','tax_id','f','f'),
  ('mychips','peers_v_flat','tax_id','base','ent','tax_id','f','f'),
  ('base','ent_v','tax_id','base','ent','tax_id','f','f'),
  ('base','ent','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('mychips','peers_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('base','addr_v_flat','ship_addr','base','addr_v_flat','ship_addr','f','f'),
  ('mychips','confirms','conf_date','mychips','confirms','conf_date','f','f'),
  ('mychips','users_v_flat','gender','base','ent','gender','f','f'),
  ('mychips','peers_v_flat','gender','base','ent','gender','f','f'),
  ('base','ent_v','gender','base','ent','gender','f','f'),
  ('base','ent','gender','base','ent','gender','f','f'),
  ('base','addr_v','addr_spec','base','addr','addr_spec','f','f'),
  ('base','addr','addr_spec','base','addr','addr_spec','f','f'),
  ('base','parm_audit','a_action','base','parm_audit','a_action','f','f'),
  ('base','ent_audit','a_action','base','ent_audit','a_action','f','f'),
  ('mychips','users_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('mychips','peers_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('base','comm_v_flat','phone_comm','base','comm_v_flat','phone_comm','f','f'),
  ('mychips','tallies','partner','mychips','tallies','partner','f','f'),
  ('base','comm_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v_flat','std_name','base','ent_v','std_name','f','f'),
  ('mychips','peers_v_flat','std_name','base','ent_v','std_name','f','f'),
  ('base','addr_v','std_name','base','ent_v','std_name','f','f'),
  ('wylib','data_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','tokens_v','std_name','base','ent_v','std_name','f','f'),
  ('base','priv_v','std_name','base','ent_v','std_name','f','f'),
  ('base','ent_v_pub','std_name','base','ent_v','std_name','f','f'),
  ('base','ent_v','std_name','base','ent_v','std_name','f','f'),
  ('wm','objects_v_depth','depth','wm','depends_v','depth','f','f'),
  ('wm','depends_v','depth','wm','depends_v','depth','f','f'),
  ('base','addr_v','addr_inact','base','addr','addr_inact','f','f'),
  ('base','addr','addr_inact','base','addr','addr_inact','f','f'),
  ('base','comm_v','mod_by','base','comm','mod_by','f','f'),
  ('mychips','users_v_flat','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','peers_v_flat','mod_by','mychips','peers','mod_by','f','f'),
  ('base','addr_v','mod_by','base','addr','mod_by','f','f'),
  ('wylib','data_v','mod_by','wylib','data','mod_by','f','f'),
  ('mychips','tokens_v','mod_by','mychips','tokens','mod_by','f','f'),
  ('base','parm_v','mod_by','base','parm','mod_by','f','f'),
  ('base','ent_v_pub','mod_by','base','ent','mod_by','f','f'),
  ('base','ent_link_v','mod_by','base','ent_link','mod_by','f','f'),
  ('wylib','data','mod_by','wylib','data','mod_by','f','f'),
  ('mychips','chits','mod_by','mychips','chits','mod_by','f','f'),
  ('mychips','tokens','mod_by','mychips','tokens','mod_by','f','f'),
  ('base','comm','mod_by','base','comm','mod_by','f','f'),
  ('mychips','users','mod_by','mychips','users','mod_by','f','f'),
  ('base','ent_v','mod_by','base','ent','mod_by','f','f'),
  ('mychips','peers','mod_by','mychips','peers','mod_by','f','f'),
  ('base','ent_link','mod_by','base','ent_link','mod_by','f','f'),
  ('mychips','tallies','mod_by','mychips','tallies','mod_by','f','f'),
  ('base','parm','mod_by','base','parm','mod_by','f','f'),
  ('base','addr','mod_by','base','addr','mod_by','f','f'),
  ('base','ent','mod_by','base','ent','mod_by','f','f'),
  ('base','addr_v','addr_cmt','base','addr','addr_cmt','f','f'),
  ('base','priv_v','priv_level','base','priv','priv_level','f','f'),
  ('base','priv','priv_level','base','priv','priv_level','f','f'),
  ('base','addr','addr_cmt','base','addr','addr_cmt','f','f'),
  ('wylib','data','owner','wylib','data','owner','f','f'),
  ('base','addr','addr_seq','base','addr','addr_seq','f','t'),
  ('base','addr','addr_ent','base','addr','addr_ent','f','t'),
  ('base','addr_prim','prim_seq','base','addr_prim','prim_seq','f','t'),
  ('base','addr_prim','prim_ent','base','addr_prim','prim_ent','f','t'),
  ('base','addr_prim','prim_type','base','addr_prim','prim_type','f','t'),
  ('base','addr_v','addr_ent','base','addr','addr_ent','f','t'),
  ('base','addr_v','addr_seq','base','addr','addr_seq','f','t'),
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
  ('base','ent_link_v','org','base','ent_link','org','f','t'),
  ('base','ent_link_v','mem','base','ent_link','mem','f','t'),
  ('base','ent_v','id','base','ent','id','f','t'),
  ('base','ent_v_pub','id','base','ent','id','f','t'),
  ('base','parm','parm','base','parm','parm','f','t'),
  ('base','parm','module','base','parm','module','f','t'),
  ('base','parm_audit','parm','base','parm_audit','parm','f','t'),
  ('base','parm_audit','a_seq','base','parm_audit','a_seq','f','t'),
  ('base','parm_audit','module','base','parm_audit','module','f','t'),
  ('base','parm_v','parm','base','parm','parm','f','t'),
  ('base','parm_v','module','base','parm','module','f','t'),
  ('base','priv','priv','base','priv','priv','f','t'),
  ('base','priv','grantee','base','priv','grantee','f','t'),
  ('base','priv_v','grantee','base','priv','grantee','f','t'),
  ('base','priv_v','priv','base','priv','priv','f','t'),
  ('mychips','chits','chit_idx','mychips','chits','chit_idx','f','t'),
  ('mychips','chits','chit_seq','mychips','chits','chit_seq','f','t'),
  ('mychips','chits','chit_ent','mychips','chits','chit_ent','f','t'),
  ('mychips','confirms','conf_idx','mychips','confirms','conf_idx','f','t'),
  ('mychips','confirms','conf_seq','mychips','confirms','conf_seq','f','t'),
  ('mychips','confirms','conf_ent','mychips','confirms','conf_ent','f','t'),
  ('mychips','covenants','version','mychips','covenants','version','f','t'),
  ('mychips','covenants','language','mychips','covenants','language','f','t'),
  ('mychips','covenants','author','mychips','covenants','author','f','t'),
  ('mychips','covenants','title','mychips','covenants','title','f','t'),
  ('mychips','peers','peer_ent','mychips','peers','peer_ent','f','t'),
  ('mychips','peers_v_flat','id','base','ent','id','f','t'),
  ('mychips','peers_v_flat','peer_ent','mychips','peers','peer_ent','f','t'),
  ('mychips','tallies','tally_ent','mychips','tallies','tally_ent','f','t'),
  ('mychips','tallies','tally_seq','mychips','tallies','tally_seq','f','t'),
  ('mychips','tokens','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','tokens','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','tokens_v','token_ent','mychips','tokens','token_ent','f','t'),
  ('mychips','tokens_v','token_seq','mychips','tokens','token_seq','f','t'),
  ('mychips','users','user_ent','mychips','users','user_ent','f','t'),
  ('mychips','users_v_flat','id','base','ent','id','f','t'),
  ('mychips','users_v_flat','peer_ent','mychips','peers','peer_ent','f','t'),
  ('mychips','users_v_flat','user_ent','mychips','users','user_ent','f','t'),
  ('wm','column_native','cnt_col','wm','column_native','cnt_col','f','t'),
  ('wm','column_native','cnt_tab','wm','column_native','cnt_tab','f','t'),
  ('wm','column_native','cnt_sch','wm','column_native','cnt_sch','f','t'),
  ('wm','column_style','cs_tab','wm','column_style','cs_tab','f','t'),
  ('wm','column_style','sw_name','wm','column_style','sw_name','f','t'),
  ('wm','column_style','cs_col','wm','column_style','cs_col','f','t'),
  ('wm','column_style','cs_sch','wm','column_style','cs_sch','f','t'),
  ('wm','column_text','language','wm','column_text','language','f','t'),
  ('wm','column_text','ct_col','wm','column_text','ct_col','f','t'),
  ('wm','column_text','ct_tab','wm','column_text','ct_tab','f','t'),
  ('wm','column_text','ct_sch','wm','column_text','ct_sch','f','t'),
  ('wm','message_text','code','wm','message_text','code','f','t'),
  ('wm','message_text','language','wm','message_text','language','f','t'),
  ('wm','message_text','mt_sch','wm','message_text','mt_sch','f','t'),
  ('wm','message_text','mt_tab','wm','message_text','mt_tab','f','t'),
  ('wm','objects','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v','release','wm','releases','release','f','t'),
  ('wm','objects_v','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v_depth','obj_nam','wm','objects','obj_nam','f','t'),
  ('wm','objects_v_depth','obj_typ','wm','objects','obj_typ','f','t'),
  ('wm','objects_v_depth','obj_ver','wm','objects','obj_ver','f','t'),
  ('wm','objects_v_depth','release','wm','releases','release','f','t'),
  ('wm','releases','release','wm','releases','release','f','t'),
  ('wm','table_style','ts_tab','wm','table_style','ts_tab','f','t'),
  ('wm','table_style','sw_name','wm','table_style','sw_name','f','t'),
  ('wm','table_style','ts_sch','wm','table_style','ts_sch','f','t'),
  ('wm','table_text','language','wm','table_text','language','f','t'),
  ('wm','table_text','tt_sch','wm','table_text','tt_sch','f','t'),
  ('wm','table_text','tt_tab','wm','table_text','tt_tab','f','t'),
  ('wm','value_text','vt_tab','wm','value_text','vt_tab','f','t'),
  ('wm','value_text','vt_col','wm','value_text','vt_col','f','t'),
  ('wm','value_text','vt_sch','wm','value_text','vt_sch','f','t'),
  ('wm','value_text','language','wm','value_text','language','f','t'),
  ('wm','value_text','value','wm','value_text','value','f','t'),
  ('wylib','data','ruid','wylib','data','ruid','f','t'),
  ('mychips','peers_v','bank','base','ent','bank','f','f'),
  ('mychips','peers_v','born_date','base','ent','born_date','f','f'),
  ('mychips','peers_v','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','peers_v','country','base','ent','country','f','f'),
  ('mychips','peers_v','crt_by','mychips','peers','crt_by','f','f'),
  ('mychips','peers_v','crt_date','mychips','peers','crt_date','f','f'),
  ('mychips','peers_v','database','base','ent','database','f','f'),
  ('mychips','peers_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','peers_v','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','peers_v','ent_name','base','ent','ent_name','f','f'),
  ('mychips','peers_v','ent_type','base','ent','ent_type','f','f'),
  ('mychips','peers_v','fir_name','base','ent','fir_name','f','f'),
  ('mychips','peers_v','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','peers_v','gender','base','ent','gender','f','f'),
  ('mychips','peers_v','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','peers_v','id','base','ent','id','f','t'),
  ('mychips','peers_v','inside','base','ent','inside','f','f'),
  ('mychips','peers_v','marital','base','ent','marital','f','f'),
  ('mychips','peers_v','mid_name','base','ent','mid_name','f','f'),
  ('mychips','peers_v','mod_by','mychips','peers','mod_by','f','f'),
  ('mychips','peers_v','mod_date','mychips','peers','mod_date','f','f'),
  ('mychips','peers_v','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','peers_v','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','peers_v','peer_ent','mychips','peers','peer_ent','f','f'),
  ('mychips','peers_v','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','peers_v','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','peers_v','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','peers_v','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','peers_v','peer_sock','mychips','peers_v','peer_sock','f','f'),
  ('mychips','peers_v','pref_name','base','ent','pref_name','f','f'),
  ('mychips','peers_v','proxy','base','ent','proxy','f','f'),
  ('mychips','peers_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','peers_v','tax_id','base','ent','tax_id','f','f'),
  ('mychips','peers_v','title','base','ent','title','f','f'),
  ('mychips','peers_v','username','base','ent','username','f','f'),
  ('mychips','users_v','bank','base','ent','bank','f','f'),
  ('mychips','users_v','born_date','base','ent','born_date','f','f'),
  ('mychips','users_v','cas_name','base','ent_v','cas_name','f','f'),
  ('mychips','users_v','country','base','ent','country','f','f'),
  ('mychips','users_v','crt_by','mychips','users','crt_by','f','f'),
  ('mychips','users_v','crt_date','mychips','users','crt_date','f','f'),
  ('mychips','users_v','database','base','ent','database','f','f'),
  ('mychips','users_v','ent_cmt','base','ent','ent_cmt','f','f'),
  ('mychips','users_v','ent_inact','base','ent','ent_inact','f','f'),
  ('mychips','users_v','ent_name','base','ent','ent_name','f','f'),
  ('mychips','users_v','ent_type','base','ent','ent_type','f','f'),
  ('mychips','users_v','fir_name','base','ent','fir_name','f','f'),
  ('mychips','users_v','frm_name','base','ent_v','frm_name','f','f'),
  ('mychips','users_v','gender','base','ent','gender','f','f'),
  ('mychips','users_v','giv_name','base','ent_v','giv_name','f','f'),
  ('mychips','users_v','host_id','mychips','users','host_id','f','f'),
  ('mychips','users_v','id','base','ent','id','f','t'),
  ('mychips','users_v','inside','base','ent','inside','f','f'),
  ('mychips','users_v','marital','base','ent','marital','f','f'),
  ('mychips','users_v','mid_name','base','ent','mid_name','f','f'),
  ('mychips','users_v','mod_by','mychips','users','mod_by','f','f'),
  ('mychips','users_v','mod_date','mychips','users','mod_date','f','f'),
  ('mychips','users_v','peer_cdi','mychips','peers','peer_cdi','f','f'),
  ('mychips','users_v','peer_cmt','mychips','peers','peer_cmt','f','f'),
  ('mychips','users_v','peer_ent','mychips','peers','peer_ent','f','f'),
  ('mychips','users_v','peer_hid','mychips','peers','peer_hid','f','f'),
  ('mychips','users_v','peer_inet','mychips','peers','peer_inet','f','f'),
  ('mychips','users_v','peer_port','mychips','peers','peer_port','f','f'),
  ('mychips','users_v','peer_pub','mychips','peers','peer_pub','f','f'),
  ('mychips','users_v','peer_sock','mychips','users_v','peer_sock','f','f'),
  ('mychips','users_v','pref_name','base','ent','pref_name','f','f'),
  ('mychips','users_v','proxy','base','ent','proxy','f','f'),
  ('mychips','users_v','std_name','base','ent_v','std_name','f','f'),
  ('mychips','users_v','tax_id','base','ent','tax_id','f','f'),
  ('mychips','users_v','title','base','ent','title','f','f'),
  ('mychips','users_v','user_cmt','mychips','users','user_cmt','f','f'),
  ('mychips','users_v','user_ent','mychips','users','user_ent','f','f'),
  ('mychips','users_v','user_inet','mychips','users','user_inet','f','f'),
  ('mychips','users_v','user_port','mychips','users','user_port','f','f'),
  ('mychips','users_v','user_sock','mychips','users_v','user_sock','f','f'),
  ('mychips','users_v','user_stat','mychips','users','user_stat','f','f'),
  ('mychips','users_v','username','base','ent','username','f','f'),
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
  ('wm','role_members','member','wm','role_members','member','f','t'),
  ('wm','role_members','role','wm','role_members','role','f','t'),
  ('wm','view_column_usage','column_name','information_schema','view_column_usage','column_name','f','f'),
  ('wm','view_column_usage','table_catalog','information_schema','view_column_usage','table_catalog','f','f'),
  ('wm','view_column_usage','table_name','information_schema','view_column_usage','table_name','f','f'),
  ('wm','view_column_usage','table_schema','information_schema','view_column_usage','table_schema','f','f'),
  ('wm','view_column_usage','view_catalog','information_schema','view_column_usage','view_catalog','f','f'),
  ('wm','view_column_usage','view_name','information_schema','view_column_usage','view_name','f','t'),
  ('wm','view_column_usage','view_schema','information_schema','view_column_usage','view_schema','f','t'),
  ('wm','fkeys_data','conname','wm','fkeys_data','conname','f','t'),
  ('wm','fkeys_data','ksf_cols','wm','fkeys_data','ksf_cols','f','f'),
  ('wm','fkeys_data','ksf_sch','wm','fkeys_data','ksf_sch','f','f'),
  ('wm','fkeys_data','ksf_tab','wm','fkeys_data','ksf_tab','f','f'),
  ('wm','fkeys_data','kst_cols','wm','fkeys_data','kst_cols','f','f'),
  ('wm','fkeys_data','kst_sch','wm','fkeys_data','kst_sch','f','f'),
  ('wm','fkeys_data','kst_tab','wm','fkeys_data','kst_tab','f','f'),
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
  ('wm','column_lang','col','wm','column_lang','col','f','t'),
  ('wm','column_lang','help','wm','column_text','help','t','f'),
  ('wm','column_lang','language','wm','column_text','language','t','f'),
  ('wm','column_lang','nat','wm','column_lang','nat','f','f'),
  ('wm','column_lang','nat_col','wm','column_native','nat_col','f','f'),
  ('wm','column_lang','nat_sch','wm','column_native','nat_sch','f','f'),
  ('wm','column_lang','nat_tab','wm','column_native','nat_tab','f','f'),
  ('wm','column_lang','obj','wm','column_lang','obj','f','f'),
  ('wm','column_lang','sch','wm','column_lang','sch','f','t'),
  ('wm','column_lang','tab','wm','column_lang','tab','f','t'),
  ('wm','column_lang','title','wm','column_text','title','t','f'),
  ('wm','column_lang','values','wm','column_lang','values','f','f'),
  ('wm','table_data','cols','wm','table_data','cols','f','f'),
  ('wm','table_data','has_pkey','wm','table_data','has_pkey','f','f'),
  ('wm','table_data','obj','wm','table_data','obj','f','f'),
  ('wm','table_data','pkey','wm','column_native','pkey','f','f'),
  ('wm','table_data','system','wm','table_data','system','f','f'),
  ('wm','table_data','tab_kind','wm','table_data','tab_kind','f','f'),
  ('wm','table_data','td_sch','wm','table_data','td_sch','f','t'),
  ('wm','table_data','td_tab','wm','table_data','td_tab','f','t'),
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
  ('wm','table_lang','columns','wm','table_lang','columns','f','f'),
  ('wm','table_lang','help','wm','table_text','help','t','f'),
  ('wm','table_lang','language','wm','table_text','language','t','t'),
  ('wm','table_lang','messages','wm','table_lang','messages','f','f'),
  ('wm','table_lang','obj','wm','table_lang','obj','f','f'),
  ('wm','table_lang','sch','wm','column_lang','sch','f','t'),
  ('wm','table_lang','tab','wm','column_lang','tab','f','t'),
  ('wm','table_lang','title','wm','table_text','title','t','f'),
  ('wm','column_def','col','wm','column_pub','col','f','t'),
  ('wm','column_def','obj','wm','column_pub','obj','f','f'),
  ('wm','column_def','val','wm','column_def','val','f','f'),
  ('wm','table_meta','cols','wm','table_data','cols','f','f'),
  ('wm','table_meta','columns','wm','table_meta','columns','f','f'),
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
  ('json','user','begin','json','user','begin','f','f'),
  ('json','user','cdi','json','user','cdi','f','f'),
  ('json','user','first','json','user','first','f','f'),
  ('json','user','id','base','ent','id','f','t'),
  ('json','user','juris','json','user','juris','f','f'),
  ('json','user','middle','json','user','middle','f','f'),
  ('json','user','name','json','user','name','f','f'),
  ('json','user','prefer','json','user','prefer','f','f'),
  ('json','user','taxid','json','user','taxid','f','f'),
  ('json','user','type','json','user','type','f','f'),
  ('mychips','tallies_v','action','mychips','tallies_v','action','f','f'),
  ('mychips','tallies_v','comment','mychips','tallies','comment','f','f'),
  ('mychips','tallies_v','contract','mychips','tallies','contract','f','f'),
  ('mychips','tallies_v','cr_limit','mychips','tallies','cr_limit','f','f'),
  ('mychips','tallies_v','crt_by','mychips','tallies','crt_by','f','f'),
  ('mychips','tallies_v','crt_date','mychips','tallies','crt_date','f','f'),
  ('mychips','tallies_v','dr_limit','mychips','tallies','dr_limit','f','f'),
  ('mychips','tallies_v','json','mychips','tallies_v','json','f','f'),
  ('mychips','tallies_v','mod_by','mychips','tallies','mod_by','f','f'),
  ('mychips','tallies_v','mod_date','mychips','tallies','mod_date','f','f'),
  ('mychips','tallies_v','part_cdi','mychips','tallies_v','part_cdi','f','f'),
  ('mychips','tallies_v','part_name','mychips','tallies_v','part_name','f','f'),
  ('mychips','tallies_v','part_sig','mychips','tallies','part_sig','f','f'),
  ('mychips','tallies_v','part_sock','mychips','tallies_v','part_sock','f','f'),
  ('mychips','tallies_v','partner','mychips','tallies','partner','f','f'),
  ('mychips','tallies_v','request','mychips','tallies','request','f','f'),
  ('mychips','tallies_v','state','mychips','tallies_v','state','f','f'),
  ('mychips','tallies_v','status','mychips','tallies','status','f','f'),
  ('mychips','tallies_v','tally_date','mychips','tallies','tally_date','f','f'),
  ('mychips','tallies_v','tally_ent','mychips','tallies','tally_ent','f','f'),
  ('mychips','tallies_v','tally_guid','mychips','tallies','tally_guid','f','f'),
  ('mychips','tallies_v','tally_seq','mychips','tallies','tally_seq','f','f'),
  ('mychips','tallies_v','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','tallies_v','user_cdi','mychips','tallies_v','user_cdi','f','f'),
  ('mychips','tallies_v','user_name','mychips','tallies_v','user_name','f','f'),
  ('mychips','tallies_v','user_sig','mychips','tallies','user_sig','f','f'),
  ('mychips','tallies_v','user_sock','mychips','tallies_v','user_sock','f','f'),
  ('mychips','tallies_v','version','mychips','tallies','version','f','f'),
  ('json','address','comment','json','address','comment','f','f'),
  ('json','address','id','json','address','id','f','t'),
  ('json','address','locale','json','address','locale','f','f'),
  ('json','address','main','json','address','main','f','f'),
  ('json','address','post','json','address','post','f','f'),
  ('json','address','prior','json','address','prior','f','f'),
  ('json','address','seq','json','address','seq','f','t'),
  ('json','address','spec','json','address','spec','f','f'),
  ('json','address','state','base','addr','state','f','f'),
  ('json','address','type','json','address','type','f','f'),
  ('json','connect','comment','json','connect','comment','f','f'),
  ('json','connect','id','json','connect','id','f','t'),
  ('json','connect','media','json','connect','media','f','f'),
  ('json','connect','prior','json','connect','prior','f','f'),
  ('json','connect','seq','json','connect','seq','f','t'),
  ('json','connect','spec','json','connect','spec','f','f'),
  ('json','tally','contract','mychips','tallies','contract','f','f'),
  ('json','tally','created','json','tally','created','f','f'),
  ('json','tally','foil','json','tally','foil','f','f'),
  ('json','tally','guid','json','tally','guid','f','f'),
  ('json','tally','id','json','tally','id','f','t'),
  ('json','tally','stock','json','tally','stock','f','f'),
  ('json','tally','version','mychips','tallies','version','f','f'),
  ('json','ticket','expires','json','ticket','expires','f','f'),
  ('json','ticket','id','base','ent','id','f','t'),
  ('json','ticket','public','json','ticket','public','f','f'),
  ('json','ticket','seq','json','ticket','seq','f','t'),
  ('json','ticket','token','mychips','tokens','token','f','f'),
  ('json','ticket','url','json','ticket','url','f','f'),
  ('mychips','chits_v','amount','mychips','chits_v','amount','f','f'),
  ('mychips','chits_v','chit_date','mychips','chits','chit_date','f','f'),
  ('mychips','chits_v','chit_ent','mychips','chits','chit_ent','f','f'),
  ('mychips','chits_v','chit_guid','mychips','chits','chit_guid','f','f'),
  ('mychips','chits_v','chit_idx','mychips','chits','chit_idx','f','f'),
  ('mychips','chits_v','chit_seq','mychips','chits','chit_seq','f','f'),
  ('mychips','chits_v','chit_type','mychips','chits','chit_type','f','f'),
  ('mychips','chits_v','crt_by','mychips','chits','crt_by','f','f'),
  ('mychips','chits_v','crt_date','mychips','chits','crt_date','f','f'),
  ('mychips','chits_v','effect','mychips','chits_v','effect','f','f'),
  ('mychips','chits_v','json','mychips','chits_v','json','f','f'),
  ('mychips','chits_v','memo','mychips','chits','memo','f','f'),
  ('mychips','chits_v','mod_by','mychips','chits','mod_by','f','f'),
  ('mychips','chits_v','mod_date','mychips','chits','mod_date','f','f'),
  ('mychips','chits_v','part_cdi','mychips','tallies_v','part_cdi','f','f'),
  ('mychips','chits_v','pro_quo','mychips','chits','pro_quo','f','f'),
  ('mychips','chits_v','request','mychips','chits','request','f','f'),
  ('mychips','chits_v','signature','mychips','chits','signature','f','f'),
  ('mychips','chits_v','state','mychips','chits_v','state','f','f'),
  ('mychips','chits_v','tally_type','mychips','tallies','tally_type','f','f'),
  ('mychips','chits_v','units','mychips','chits','units','f','f'),
  ('mychips','chits_v','user_cdi','mychips','tallies_v','user_cdi','f','f'),
  ('mychips','chits_v','value','mychips','chits_v','value','f','f'),
  ('json','users','addresses','json','users','addresses','f','f'),
  ('json','users','begin','json','user','begin','f','f'),
  ('json','users','cdi','json','user','cdi','f','f'),
  ('json','users','connects','json','users','connects','f','f'),
  ('json','users','first','json','user','first','f','f'),
  ('json','users','juris','json','user','juris','f','f'),
  ('json','users','middle','json','user','middle','f','f'),
  ('json','users','name','json','user','name','f','f'),
  ('json','users','prefer','json','user','prefer','f','f'),
  ('json','users','taxid','json','user','taxid','f','f'),
  ('json','users','type','json','user','type','f','f');

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
insert into base.ent (ent_name,ent_type,username,database,country) values ('Admin','r',session_user,true,'US');
select base.priv_grants();
insert into base.parm_v (module,parm,type,value,cmt) values ('mychips','mobi_port','int','12345','Default port where mobile application connects.');
insert into base.parm_v (module,parm,type,value,cmt) values ('mychips','mobi_inet','text','192.168.58.102','Default IP where mobile application connects.');
insert into base.parm_v (module,parm,type,value,cmt) values ('mychips','cert_days','int','14','Default number of days for a certificate to be valid.');

