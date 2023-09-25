-- Build sample schema for testing pathfinding cache

-- Cache/map of existing pathways through our data
-- ath: path of nodes, minus the first node in the path
-- eids: array of edge IDs in the path
-- enorm: array of edge ID's, normalized to reveal equivalent paths
-- cycle: this path is a circuit
drop table if exists paths cascade;
create table if not exists paths (
    pid		serial	primary key
  , inp		text	not null references nodes on update cascade on delete cascade
  , out		text	not null references nodes on update cascade on delete cascade
  , ath		text[]	not null
  , eids	int[]	not null unique
  , enorm	int[]	not null
  , cycle	boolean	not null default false
);

-- Convert array of eid's to an array of node pairs
-- ----------------------------------------------------------------
create or replace function eid2nn(eids_array int[])
returns text[] language plpgsql as $$
  declare
    node_pair text;
    node_pairs text[];
    edge_record record;
  begin
    for i in array_lower(eids_array, 1)..array_upper(eids_array, 1) loop
      select inp, out into edge_record from edges where eid = eids_array[i];
      if edge_record is not null then
        node_pair := edge_record.inp || edge_record.out;
        node_pairs := array_append(node_pairs, node_pair);
      end if;
    end loop;
    return node_pairs;
  end;
$$;

create or replace view paths_v as
  select *,
  p.inp || p.ath as path,	-- Create a field to show full path
  eid2nn(p.eids) as enn		-- Render edges as their node end-points
  from paths p;

-- Link table for querying complex path relationships
drop table if exists links cascade;
create table if not exists links (
    pid		int	references paths on update cascade on delete cascade
  , edge	int	references edges on update cascade on delete cascade
  , index	int	not null check (index > 0)
  , unique (pid, edge)
);

-- Automatically populate the normalized edges array field
create or replace function paths_tbf() returns trigger language plpgsql as $$
  begin
    new.enorm = edges_norm(new.eids, new.cycle);
    return new;
  end;
$$;
drop trigger if exists paths_tbr on paths;
create trigger paths_tbr before insert or update of eids on paths
  for each row execute function paths_tbf();

-- Automatically generate/maintain contents the link table
create or replace function paths_taf() returns trigger language plpgsql as $$
  declare
    eid int;
    count int = 1;
  begin
    for eid in select unnest(new.eids) loop
      insert into links (pid, edge, index) values (new.pid, eid, count)
      on conflict (pid, edge) do update set index = count;
      count = count + 1;
    end loop;
    delete from links where pid = new.pid and index > array_length(new.eids, 1);
    return new;
  end;
$$;
drop trigger if exists paths_tar on paths;
create trigger paths_tar after insert or update of pid, eids on paths
  for each row execute function paths_taf();

-- Delete any paths that include edges not in our edge table (quality check)
-- ----------------------------------------------------------------
create or replace function edges_missing() 
  returns int language plpgsql as $$
  declare
    rows int;
  begin
    with orphaned_eids as (
      select distinct unnest(eids) as eid from paths
      except select eid from edges
    ),
    orphaned_paths as (
      select pid from paths, orphaned_eids
      where  orphaned_eids.eid = any(paths.eids)
    )
    delete from paths where pid in (select pid from orphaned_paths);
    get diagnostics rows = ROW_COUNT;
    return rows;
  end;
$$;

-- Insert path for any edges not already found somewhere in the path table
-- ----------------------------------------------------------------
create or replace function paths_missing() 
  returns int language plpgsql as $$
  declare
    rows int;
  begin
   insert into paths (inp, out, ath, eids)
     select e.inp, e.out, array[e.out], array[e.eid]
     from edges e where not exists (
       select 1 from links l where l.edge = e.eid
     );
    get diagnostics rows = ROW_COUNT;
    return rows;
  end;
$$;

-- Lengthen existing paths by one link where possible
-- ----------------------------------------------------------------
create or replace function paths_search()
  returns int language plpgsql as $$
  declare
    rows int;
  begin
    with paths_old as (select * from paths)
  , edges_both as (
      select eid, inp, out from edges union all
      select eid, out as inp, inp as out from edges
    )
  , paths_new as (
      select p.pid, p.inp, e.out,
        p.ath || array[e.out] as ath,
        p.eids || array[e.eid] as eids,
        (p.inp = e.out) as cycle
      from paths_old p
      join edges_both e on p.out = e.inp
      where e.out != all(p.ath)			-- Can't re-cross an edge
        and e.out != coalesce(p.ath[array_upper(p.ath, 1) - 1], p.inp)	-- Don't search where we just came from
        and not p.cycle				-- Don't try to expand existing cycles
    )
  , inserted as (
      insert into paths (inp, out, ath, eids, cycle)
      select inp, out, ath, eids, cycle
      from paths_new
      on conflict (eids) do nothing
      returning *
    ), 
    deleted as (
      delete from paths using paths_new where paths.pid = paths_new.pid
    )
    select count(*) into rows from inserted;
    return rows;
  end;
$$;

-- Generic array reverse function
-- ----------------------------------------------------------------
create or replace function array_reverse(anyarray)
returns anyarray strict immutable language sql as $$
  select array(
    select $1[i]
    from generate_subscripts($1, 1) as s(i)
    order by i desc
  );
$$;

-- Order edge array in a standard way
-- Linear paths are considered equal regardless of the direction
-- Cyclical paths are considered equal regardless of direction or starting point
-- ----------------------------------------------------------------
create or replace function edges_norm(eids int[], is_cycle boolean)
returns int[] immutable language plpgsql as $$
  declare
    normed int[] = eids;
    min_element int;
    min_index int;
    length int = array_length(eids,1);
  begin

    if is_cycle then		-- cycles: find smallest edge
      select min(elem) into min_element from unnest(eids) as elem;
      min_index := array_position(eids, min_element);
      if min_index > 1 then	-- rotate smallest into position 1
        normed := eids[min_index:length] || eids[1:min_index-1];
      end if;

      if normed[2] > normed[length] then	-- make element 2 next smallest
        normed := normed[1] || array_reverse(normed[2:length]);
      end if;
    else			-- linear: start_edge < end_edge
      if eids[length] < eids[1] then
        normed = array_reverse(normed);
      end if;
    end if;

    return normed;
  end;
$$;

-- Return paths that are redundant and can be deleted
-- ----------------------------------------------------------------
create or replace function path_dups()
  returns setof paths language sql as $$
  with duplicates as (
    select enorm,
      min(case when eids = enorm then pid else null end) as natural_norm,
      min(pid) as min_pid
    from paths group by enorm having count(*) > 1
  )
  select p.*
    from paths p
    join duplicates d on p.enorm = d.enorm
    where p.pid != coalesce(d.natural_norm, d.min_pid)
$$;

-- Delete redundant paths
-- ----------------------------------------------------------------
create or replace function delete_dups()
  returns int language plpgsql as $$
  declare
    rows int;
  begin
    delete from paths where pid in (select pid from path_dups());
    get diagnostics rows = ROW_COUNT;
    return rows;
  end;
$$;

-- Return paths that are sub-paths of other existing paths
-- ----------------------------------------------------------------
create or replace function path_subs()
  returns table (pid int) language sql as $$
    with initial_filter as (
      select a.pid as apid, b.pid as bpid
      from paths a
      join paths b on a.eids @> b.eids and a.pid != b.pid
      where b.cycle is false
    ),
    ordered_check as (
      select f.apid, f.bpid, a.index as aindex, b.index as bindex
      from links a
      join links b on a.edge = b.edge
      join initial_filter f on a.pid = f.apid and b.pid = f.bpid
    ),
    diff_check as (
      select apid, bpid, max(aindex - bindex) as max_diff, min(aindex - bindex) as min_diff
      from ordered_check
      group by apid, bpid
    )
    select distinct bpid as pid from diff_check where max_diff = min_diff;
$$;

-- Delete redundant paths
-- ----------------------------------------------------------------
create or replace function delete_subs()
  returns int language plpgsql as $$
  declare
    rows int;
  begin
    delete from paths where pid in (select pid from path_subs());
    get diagnostics rows = ROW_COUNT;
    return rows;
  end;
$$;

-- Find paths that are a sub-path of a longer path
-- ----------------------------------------------------------------
create or replace function delete_subsX(anyarray)
returns anyarray strict immutable language sql as $$
  with initial_filter as (
    select a.pid as apid, b.pid as bpid, a.eids as aeids, b.eids as beids
    from paths a, paths b
    where a.eids @> b.eids and a.pid != b.pid
  ),
  ordered_check as (
    select apid, bpid, aeids, beids,
           row_number() over (partition by apid, bpid order by aidx) as arow,
           row_number() over (partition by apid, bpid order by bidx) as brow
    from initial_filter
         cross join lateral unnest(aeids) with ordinality as a(e, aidx)
         cross join lateral unnest(beids) with ordinality as b(e, bidx)
    where position(b.e in aeids) > 0
  ),
  to_delete as (
    select bpid
    from ordered_check
    group by apid, bpid
    having max(arow - brow) = min(arow - brow) and min(arow - brow) >= 0
  )
  delete from paths where pid in (select bpid from to_delete);
$$;

-- Discover all pathways beginning from a specified node
--function {mychips.tallies_node_path2(tally uuid)} {mychips.users_v mychips.tallies_v_net} {
-- returns table (
--   inp text, "out" text, edges int, ath text[], circuit boolean, path text[]
-- ) language sql as $$
--  with recursive 
--  tallies as (
--    select distinct tally_ent as inp, part_ent as out
--    from mychips.tallies where status = 'open'
--  ),
--  tally_path (
--      inp, out, edges, ath, circuit
--    ) as (
--      select inp, out, 1, array[out], false
--    from	tallies
--    where	to.uuid = tally
--  union all
--    select tp.inp					as inp
--      , ty.out						as out
--      , tp.edges + 1					as edges
--      , tp.ath || ty.out				as ath
--      , coalesce(tp.inp = ty.out, false)		as circuit
--
--    from	tallies		ty
--    join	tally_path	tp on tp.out = ty.inp
--    		and not ty.out = any(tp.ath)
--    where	-- t.canlift and
--    		tp.edges <= base.parm('paths', 'maxlen', 10)
--  ) select tx.inp, tx.out, tx.edges, tx.ath, tx.circuit
--    , tx.inp || tx.ath		as path
--
--  from	tally_path tx
--$$;}
