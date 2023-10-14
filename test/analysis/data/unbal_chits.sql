-- Chits that have different amounts on their two ends

with tran_chits as (
  select * from mychips.chits where chit_type = 'tran'
)
select cs.chit_ent, cs.chit_seq, cs.chit_idx, cs.units,
       cf.chit_ent, cf.chit_seq, cf.chit_idx, cf.units
  from		tran_chits cs
  join		tran_chits cf on cs.chit_uuid = cf.chit_uuid
                  and cs.chit_ent != cf.chit_ent
  where cs.units != cf.units
;
