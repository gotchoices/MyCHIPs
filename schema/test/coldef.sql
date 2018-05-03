select string_agg(val,',') from wm.column_def where obj = 'base.ent' returning *;


--select string_agg(sq.cmd,',') from (
--select
--  case when def is not null then
--    'coalesce($1.' || col || ',' || def || ') as ' || col
--  else
--    '$1.' || col || ' as ' || col
--  end as cmd
--    from wm.column_pub where obj = 'base.ent' order by field
--    ) as sq
--;
