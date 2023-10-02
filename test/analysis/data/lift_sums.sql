-- Effect of lift chits on users' tallies

select chit_ent,chit_uuid,sum(net) from mychips.chits_v 
  where chit_type = 'lift'
  group by 1,2
  order by 3,2,1;
