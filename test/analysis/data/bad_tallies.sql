-- Tally pairs left in indeterminate states
with tally_aggs as (
select
  tally_uuid, 
  array_agg(tally_ent) as ents,
  array_agg(tally_type) as types,
  array_agg(status) as stats,
  count(*)
  
  from mychips.tallies_v
  group by 1
  having count(*) = 2
) select * from tally_aggs
  where 'open' != any(stats)
;  
