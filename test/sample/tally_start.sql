--Initiate a tally for user 10001

--delete from mychips.tallies where status in ('void', 'draft');
delete from mychips.tallies;

insert into mychips.tallies
  (tally_ent, tally_guid, partner, user_sig)
values
  (10001, '18d44de5-837d-448f-8d96-9136372987cf',10000,'Adam signature');

-- Only update triggers look for requests
update mychips.tallies set request = 'draft' where tally_ent = 10001 and status = 'void';

select user_cid, part_cid, tally_type, state from mychips.tallies_v;
