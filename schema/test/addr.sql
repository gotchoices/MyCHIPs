insert into base.addr_v (addr_ent,addr_spec,city,state,pcode,country)
  values (1001,'3456 A Street','Chicago','IL',65432,'US')
  returning *
;
