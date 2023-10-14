-- Chits that exist on only one side of a tally

with stray_chits as (
  select chit_uuid, count(*) from mychips.chits 
    where chit_type = 'tran'
    group by 1 having count(*) < 2
)
select c.chit_ent, c.chit_seq, c.chit_idx, c.chit_type, c.chain_idx, c.chit_uuid
  from		mychips.chits c
  join		stray_chits sc on sc.chit_uuid = c.chit_uuid
;
