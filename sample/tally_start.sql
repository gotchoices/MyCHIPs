--Initiate a tally for user 10001

delete from mychips.tallies where tally_ent = 10001 and status in ('void', 'draft');

insert into mychips.tallies
  (tally_ent, tally_guid, partner, user_sig)
values
  (10001, '18d44de5-837d-448f-8d96-9136372987cf',10002,'User signature');

update mychips.tallies set request = 'draft' where tally_ent = 10001 and status = 'void';
