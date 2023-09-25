-- Create a simple starting point for cache data

insert into paths (inp, out, ath, eids) values 
  ('a', 'b', array['b'], array[1]),
  ('b', 'd', array['c','d'], array[2,5]);

-- select paths_missing();
