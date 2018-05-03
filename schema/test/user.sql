insert into mychips.users_v 
  (ent_name,user_port,born_date) 
values
  ('Smith',1234,'1970-Jan-03')
returning *;

--insert into base.ent
--  (ent_name,ent_type) 
--values
--  ('Garvin',coalesce(null,default))
