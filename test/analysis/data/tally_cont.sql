-- Tallies and their contracts

select tally_ent,tally_seq,tally_type,status,contract,crt_date from mychips.tallies
  order by 1,2,3
