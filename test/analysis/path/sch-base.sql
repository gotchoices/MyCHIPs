-- Basic schema containing nodes and edges

drop table if exists nodes cascade;
create table if not exists nodes (
   name		text	primary key
);

drop table if exists edges cascade;
create table if not exists edges (
   eid		serial	primary key
 , inp		text	not null references nodes on update cascade on delete cascade
 , out		text	not null references nodes on update cascade on delete cascade
);

-- Create random graph data set
-- Usage: select random_graph(nodes, edges)
-- ----------------------------------------------------------------
create or replace function random_graph(N integer, E integer)
returns void language plpgsql as $$
declare
  i integer;
  inp_node text;
  out_node text;
begin
  -- Add N nodes
  for i in 1..N loop
    insert into nodes (name) values ('n' || i)
    on conflict (name) do nothing;
  end loop;
  
  -- Add E edges
  for i in 1..E loop
    -- Randomly select input and output nodes
    select name into inp_node from nodes offset floor(random() * N) limit 1;
    select name into out_node from nodes offset floor(random() * N) limit 1;
  
    -- Ensure that the inp_node and out_node are different
    while inp_node = out_node loop
      select name into out_node from nodes offset floor(random() * N) limit 1;
    end loop;

    -- Insert the edge
    insert into edges (inp, out) values (inp_node, out_node);
  end loop;
end;
$$;
