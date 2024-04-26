-- Basic schema containing nodes and edges

drop table if exists nodes cascade;
create table if not exists nodes (
   name		text	primary key
);

drop table if exists edges cascade;
create table if not exists edges (
   eid		serial	primary key
 , w		int	not null default floor(random() * 200) - 100
 , inp		text	not null references nodes on update cascade on delete cascade
 , out		text	not null references nodes on update cascade on delete cascade
);
create or replace view edges_both as
  select eid, inp, out, w, 1 as dir from edges
  union all
  select eid, out as inp, inp as out, -w as w, -1 as dir from edges;

create index if not exists edges_inp_idx on edges (inp) include (out);
create index if not exists edges_out_idx on edges (out) include (inp);

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
  
    -- Ensure that the inp_node and out_node are different
    out_node := inp_node;
    while inp_node = out_node loop
      select name into out_node from nodes offset floor(random() * N) limit 1;
    end loop;

    -- Insert the edge
    insert into edges (inp, out) values (inp_node, out_node);
  end loop;
end;
$$;

-- Create nodes with specific number of edges each (referencing only nodes below "starting")
-- Usage: select random_supernodes(node_count, edges_each, starting)
-- ----------------------------------------------------------------
create or replace function random_supernodes(node_count int, edges_each int, starting int = 1)
returns void language plpgsql as $$
declare
  i int;
  j int;
  inp_node text;
  out_node text;
begin
  -- Add N nodes
  for i in starting..(starting + node_count) loop
    insert into nodes (name) values ('n' || i)
      on conflict (name) do nothing;
  end loop;
  
  -- For each node, add edges
  for i in starting..(starting + node_count) loop
    inp_node := 'n' || i;
    for j in 1..edges_each loop
      -- Ensure that the inp_node and out_node are different
      out_node := inp_node;
      while inp_node = out_node loop
        select name into out_node from nodes offset floor(random() * starting) limit 1;
      end loop;

      -- Insert the edge
      insert into edges (inp, out) values (inp_node, out_node);
    end loop;
  end loop;
end;
$$;

-- Create nodes with cluster_prob chance of being connected within a cluster defined by multiples of cluster_size
-- Usage: select random_clustered(node_count, edge_count, cluster_size, cluster_prob)
-- ----------------------------------------------------------------
-- drop function if exists random_clustered(int, int, int, float);
create or replace function random_clustered(node_count int, edge_count int, cluster_size int, cluster_prob float)
returns void language plpgsql as $$
declare
  i int;
  j int;
  inp_index int;
  out_index int;
  inp_node text;
  out_node text;
begin
  if not cluster_prob between 0 and 1 then
    raise exception 'cluster_prob must be between 0 and 1';
  end if;

  -- Add N nodes
  for i in 1..node_count loop
    insert into nodes (name) values ('n' || i)
      on conflict (name) do nothing;
  end loop;
  
  -- Add E edges with cluster_prob chance of being connected within a cluster
  for i in 1..edge_count loop
    -- Randomly select input 
    inp_index := floor(random() * node_count);
    select name into inp_node from nodes offset inp_index limit 1;

    out_node := inp_node;
    if random() < cluster_prob then -- Connect to a node within the same cluster?
      while inp_node = out_node loop
        -- Randomly select output within the same cluster
        out_index := inp_index + floor(random() * cluster_size) - floor(cluster_size / 2);
        if out_index < 0 then
          out_index := 0;
        elsif out_index >= node_count then
          out_index := node_count - 1;
        end if;
        select name into out_node from nodes offset out_index limit 1;
      end loop;
    else  -- Connect to a random node
      while inp_node = out_node loop
        -- Randomly select output from the entire set of nodes
        select name into out_node from nodes offset floor(random() * node_count) limit 1;
      end loop;
    end if;

    -- Insert the edge
    insert into edges (inp, out) values (inp_node, out_node);
  end loop;
end;
$$;
