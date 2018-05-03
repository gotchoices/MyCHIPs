--create or replace function testcomp() returns table (int,varchar) as $$
create or replace function testcomp() returns int as $$
  declare
--    v	table (a int,b varchar);
  begin
    v = (5,7);
    return 3;
  end;
$$ language plpgsql;
