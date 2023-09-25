-- Build sample schema for testing pathfinding cache

-- Cache/map of existing pathways through our data
-- ath: path of nodes, minus the first node in the path
-- eids: array of edge IDs in the path
-- enorm: array of edge ID's, normalized to reveal equivalent paths
-- cycle: this path is a circuit
-- term: can't expand any more right now
drop table if exists paths cascade;
create table if not exists paths (
    pid		serial	primary key
  , inp		text	not null references nodes on update cascade on delete cascade
  , out		text	not null references nodes on update cascade on delete cascade
  , ath		text[]	not null
  , eids	int[]	not null unique
  , enorm	int[]	not null
  , cycle	boolean	not null default false
  , term	boolean	not null default false
);
create index idx_array_length on paths (array_length(eids, 1));
create index idx_cycle on paths (cycle);

-- Convert array of eid's to an array of node pairs
-- ----------------------------------------------------------------
create or replace function eid2nn(eids_array int[])
returns text[] language plpgsql as $$
  declare
    node_pair text;
    node_pairs text[];
    edge_record record;
  begin
    for i in array_lower(eids_array, 1)..array_upper(eids_array, 1) loop
      select inp, out into edge_record from edges where eid = eids_array[i];
      if edge_record is not null then
        node_pair := edge_record.inp || edge_record.out;
        node_pairs := array_append(node_pairs, node_pair);
      end if;
    end loop;
    return node_pairs;
  end;
$$;

-- Expanded view of paths
-- ----------------------------------------------------------------
create or replace view paths_v as
  select *,
  p.inp || p.ath as path,	-- Create a field to show full path
  eid2nn(p.eids) as enn		-- Render edges as their node end-points
  from paths p;

-- Link table for querying complex path relationships
-- ----------------------------------------------------------------
drop table if exists links cascade;
create table if not exists links (
    pid		int	references paths on update cascade on delete cascade
  , edge	int	references edges on update cascade on delete cascade
  , index	int	not null check (index > 0)
  , unique (pid, edge)
);

-- Automatically populate the normalized edges array field
-- ----------------------------------------------------------------
create or replace function paths_tbf() returns trigger language plpgsql as $$
  begin
    new.enorm = edges_norm(new.eids, new.cycle);
    return new;
  end;
$$;
drop trigger if exists paths_tbr on paths;
create trigger paths_tbr before insert or update of eids on paths
  for each row execute function paths_tbf();

-- Automatically generate/maintain contents the link table
-- ----------------------------------------------------------------
create or replace function paths_taf() returns trigger language plpgsql as $$
  declare
    eid int;
    count int = 1;
  begin
    for eid in select unnest(new.eids) loop
      insert into links (pid, edge, index) values (new.pid, eid, count)
      on conflict (pid, edge) do update set index = count;
      count = count + 1;
    end loop;
    delete from links where pid = new.pid and index > array_length(new.eids, 1);
    return new;
  end;
$$;
drop trigger if exists paths_tar on paths;
create trigger paths_tar after insert or update of pid, eids on paths
  for each row execute function paths_taf();
