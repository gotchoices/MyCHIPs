--User 10000 signs chit in acceptance of payment request

update mychips.chits set request = 'userAccept', signature = 'James signature' where chit_ent = 10000 and signature is null;

select chit_guid, chit_date, signature, state from mychips.chits_v;
