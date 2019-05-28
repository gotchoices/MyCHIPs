--Insert some dummy tallies for development purposes

insert into mychips.chits
  (chit_ent, chit_seq, chit_guid, chit_type, signature, units)
values 
  ('p1001', 1, 'bd2150c3-e064-42e9-996f-20cae81e18bc', 'tran', 'Adam Signature',  100000),
  ('p1000', 1, 'bd2150c3-e064-42e9-996f-20cae81e18bc', 'tran', 'James Signature',  100000),
  ('p1000', 2, 'fd6afdf4-6809-46d1-a2ce-b1d67bbbdb40', 'tran', 'James Signature', 200000),
  ('p1002', 2, 'fd6afdf4-6809-46d1-a2ce-b1d67bbbdb40', 'tran', 'Fran Signature', 200000);
