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
    with paths_old as (
      update paths set term = true
        returning pid, inp, out, ath, eids, cycle, term
    )
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
      where not b.cycle
--      and not a.term		-- Doesn't seem to speed anything up
--      and b.term
      and b.eids[1] = any(a.eids)
      and array_length(a.eids,1) > array_length(b.eids,1)
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
-- ----------------------------------------------------------------
create or replace function path_find(start_node text, end_node text, minw int, max int = 10)
returns table (
  inp text, "out" text, ecnt int, ath text[], min int, circuit boolean, found boolean, path text[]
) language sql as $$
  with recursive 
  edges_both as (
      select eid, inp, out, w from edges union all
      select eid, out as inp, inp as out, -w as w from edges
  ),
  find_path (
      inp, out, ecnt, ath, min, circuit, found
    ) as (
      select inp, out, 1, array[out], w, false, false
    from	edges_both
    where	w >= minw
    and		inp = start_node
  union all
    select fp.inp				as inp
      , e.out					as out
      , fp.ecnt + 1				as ecnt
      , fp.ath || e.out				as ath
      , least(fp.min, e.w)			as min
      , coalesce(fp.inp = e.out, false)		as circuit
      , e.out = end_node			as found

    from	edges_both	e
    join	find_path	fp on fp.out = e.inp
    		and not e.out = any(fp.ath)
    where	fp.ecnt < max
    and		e.w >= minw
    and		not fp.found
  ) select p.inp, p.out, p.ecnt, p.ath, p.min, p.circuit, p.found
    , p.inp || p.ath		as path

  from find_path p
$$;

-- Discover all pathways
-- ----------------------------------------------------------------
create or replace view path_finder as
  with recursive 
  edges_both as (
      select eid, inp, out, w from edges union all
      select eid, out as inp, inp as out, -w as w from edges
  ),
  find_path (
      inp, out, ecnt, ath, min, circuit
    ) as (
      select inp, out, 1, array[out], w, false
    from	edges_both
    where	w > 0
  union all
    select fp.inp				as inp
      , e.out					as out
      , fp.ecnt + 1				as ecnt
      , fp.ath || e.out				as ath
      , least(fp.min, e.w)			as min
      , coalesce(fp.inp = e.out, false)		as circuit

    from	edges_both	e
    join	find_path	fp on fp.out = e.inp
    		and not e.out = any(fp.ath)
    where	fp.ecnt <= 99
    and		e.w > 0
  ) select p.inp, p.out, p.ecnt, p.ath, p.min, p.circuit
    , p.inp || p.ath		as path

  from find_path p;
