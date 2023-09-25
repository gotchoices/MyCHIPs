
-- Discover all pathways beginning from a specified node
-- ----------------------------------------------------------------
create or replace function path_find(start_node text, size int, max int = 10)
returns table (
  inp text, "out" text, ecnt int, ath text[], min int, circuit boolean, path text[]
) language sql as $$
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
    where	inp = start_node
--    and		w >= size
  union all
    select fp.inp					as inp
      , e.out						as out
      , fp.ecnt + 1					as ecnt
      , fp.ath || e.out				as ath
      , least(fp.min, e.w)			as min
      , coalesce(fp.inp = e.out, false)		as circuit

    from	edges_both	e
    join	find_path	fp on fp.out = e.inp
    		and not e.out = any(fp.ath)
    where	true	 --	w >= size
    and		fp.ecnt <= max
  ) select p.inp, p.out, p.ecnt, p.ath, p.min, p.circuit
    , p.inp || p.ath		as path

  from find_path p
$$;
