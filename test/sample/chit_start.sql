--Initiate a chit for user 10001

--delete from mychips.tallies where status in ('void', 'draft');
delete from mychips.chits;

insert into mychips.chits
  (chit_ent, chit_seq, chit_guid, units, memo)
values
  (10001, 1, '4de5aec0-713f-45f9-a3c5-ad9e7829b764', 1234567800, 'Test transaction');

-- Only update triggers look for requests
update mychips.chits set request = 'userRequest' where chit_ent = 10001 and chit_seq = 1;

select chit_ent, chit_seq, chit_idx, chit_type, amount, state from mychips.chits_v;
