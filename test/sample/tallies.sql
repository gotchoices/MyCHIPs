--Insert some dummy tallies for development purposes

insert into mychips.tallies
  (tally_ent, tally_seq, tally_guid, tally_type, tally_date, version, partner, status, user_sig, part_sig)
values 
  ('p1001', 1, '18d44de5-837d-448f-8d96-9136372987cf', 'stock', '2018-11-10', 1, 'p1000', 'open', 'Adam Signature',  'James Signature'),
  ('p1000', 1, '18d44de5-837d-448f-8d96-9136372987cf', 'foil',  '2018-11-10', 1, 'p1001', 'open', 'James Signature', 'Adam Signature'),
  ('p1002', 1, 'a666a319-e6cd-11e8-9d2c-000000000929', 'stock', '2018-11-11', 1, 'p1001', 'open', 'Fran Signature',  'Adam Signature'),
  ('p1001', 2, 'a666a319-e6cd-11e8-9d2c-000000000929', 'foil',  '2018-11-11', 1, 'p1002', 'open', 'Adam Signature',  'Fran Signature'),
  ('p1000', 2, '9a2cdd6c-e6cd-11e8-91b8-0800273cd2c6', 'stock', '2018-11-12', 1, 'p1002', 'open', 'James Signature', 'Fran Signature'),
  ('p1002', 2, '9a2cdd6c-e6cd-11e8-91b8-0800273cd2c6', 'foil',  '2018-11-12', 1, 'p1000', 'open', 'Fran Signature',  'James Signature'),
  ('p1000', 3, '7bccf120-e9bd-11e8-b956-0800273cd2c6', 'foil',  '2018-11-13', 1, 'o500',  'open', 'James Signature', 'Ahoy Signature'),
  ('o500',  1, '7bccf120-e9bd-11e8-b956-0800273cd2c6', 'stock', '2018-11-13', 1, 'p1000', 'open', 'Ahoy Signature',  'James Signature'),
  ('p1001', 3, '6bf1c41e-e9be-11e8-9c70-0800273cd2c6', 'stock', '2018-11-14', 1, 'o500',  'open', 'Adam Signature',  'Ahoy Signature'),
  ('o500',  2, '6bf1c41e-e9be-11e8-9c70-0800273cd2c6', 'foil',  '2018-11-14', 1, 'p1001', 'open', 'Ahoy Signature',  'James Signature');
