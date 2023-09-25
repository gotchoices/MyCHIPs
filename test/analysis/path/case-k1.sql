-- A simple test case graph network

insert into nodes (name) values
  ('a'),
  ('b'),
  ('c'),
  ('d'),
  ('e');

insert into edges (inp, out) values
  ('a', 'b'),
  ('b', 'c'),
  ('a', 'c'),
  ('a', 'd'),
  ('c', 'd'),
  ('d', 'e');
