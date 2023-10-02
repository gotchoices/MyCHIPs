-- HACK: node_path structure is work around for bug in pgsql involving nested arrays
drop type if exists node_path;
create type node_path AS (
    node text,
    path text[]
);

-- Breadth First Traversal (BFT) using array
create or replace function find_target_array_via_bft(start_node text, target_node text)
returns text[] language plpgsql as $$
declare
    edge record;
    current node_path;
    queue node_path[]; 
begin
    queue := array[row(start_node, array[start_node])::node_path]; -- Initialize with start node and its path

    while array_length(queue, 1) > 0 loop
--        RAISE NOTICE 'Queue: %', queue;

        current := queue[1];
        queue := queue[2:array_upper(queue, 1)]; 

        for edge in (
            select out node from edges where inp = current.node and out <> all(current.path)
            union all
            select inp node from edges where out = current.node and inp <> all(current.path)
        )
        loop
            if edge.node = target_node then
                return current.path || edge.node;
            end if;
            
            queue := queue || array[row(edge.node, current.path || edge.node)::node_path];
        end loop;
    end loop;

    return null;
end;
$$;

-- Temp table version of BFT
create or replace function find_target_table_via_bft(start_node text, target_node text)
returns text[] language plpgsql as $$
declare
    edge record;
    current_path text[];
    current_node text;
    queue_id integer;
begin
    drop table if exists queue;
    drop sequence if exists queue_id_seq;
    create temp sequence queue_id_seq;
    create temp table queue(
        id integer primary key default nextval('queue_id_seq'),
        path text[]
    );
    insert into queue(path) values (array[start_node]);

    while exists (select 1 from queue) loop
        -- Dequeue the oldest path from the queue using the primary key for efficiency
        select id, path, path[array_upper(path, 1)] into queue_id, current_path, current_node from queue order by id asc limit 1;
        delete from queue where id = queue_id;

--        RAISE NOTICE 'Path: % %', queue_id, current_path;

        -- Check both directions for edges
        for edge in (
            select out as node from edges where inp = current_node and out <> ALL(current_path)
            union all
            select inp as node from edges where out = current_node and inp <> ALL(current_path)
        ) loop
            -- If we find the target node, return the path
            if edge.node = target_node then
                return current_path || edge.node;
            end if;

            -- Enqueue the new path
            insert into queue(path) values (current_path || edge.node);
        end loop;
    end loop;

    -- Cleanup
    drop table if exists queue;
    drop sequence if exists queue_id_seq;

    return null;  -- if target_node is not reached
end;
$$;

-- BFT Version which uses an insert statement at each level.  Returns ties at return level.
create or replace function find_target_multi_via_bft(start_node text, target_node text, minw integer default 0, max_depth integer default 10)
returns table(path text[]) language plpgsql as $$
declare
    depth integer := 1;
begin
    -- Create current and next level tables to simulate queue behavior
    drop table if exists levels;
    drop sequence if exists bft_seq;
    create temp sequence bft_seq;

    create temp table levels(
        id integer default nextval('bft_seq'),
        level integer,
        node text, -- last node in path (for efficiency in finding)
        path text[],
        primary key (level, node, id) include (path)
    );
    
    insert into levels(level, node, path) values (1, start_node, array[start_node]);

    while exists (select 1 from levels where level = depth) and depth <= max_depth loop
--        RAISE NOTICE '%: Path: %', depth, (select string_agg(array_to_string(cl.path, ','), ';  ') from levels cl where cl.level = depth);

        -- Insert neighbors into the next level if they haven't been visited
        insert into levels(level, node, path)
            select distinct depth + 1, e.target, array_append(cl.path, e.target)
            from levels cl
            join (
                select out as source, inp as target from edges where w <= -minw
                union all
                select inp as source, out as target from edges where w >= minw
            ) e on e.source = cl.node and e.target <> all(cl.path)
            where cl.level = depth;

        -- If the target node is one of the new paths, return the path
        if exists (select 1 from levels q where q.level = depth and q.node = target_node) then
            return query select q.path from levels q where q.level = depth and q.node = target_node;
            exit;
        end if;

        -- Clean up the current level
        delete from levels where level = depth;

        depth := depth + 1;
    end loop;

    -- Cleanup
    drop table if exists levels;
    drop sequence if exists bft_seq;

    return query select null::text[] as path;  -- if target_node is not reached
end;
$$;

-- Optimized BFT Version one iteration faster that can also detect cycles
create or replace function find_target_multi_via_bfto(start_node text, target_node text, minw integer default 0, max_depth integer default 10)
returns table (
  id integer,
  level integer,
  first text,
  last text,
  ath text[],
  eids int[]
) language plpgsql as $$
  declare
    depth integer := 1;
  begin
    drop table if exists levels;	-- Create current/next level table to simulate queue behavior
    create temp table levels (
        id serial,
        level integer,
        first text,
        last text,
        ath text[],
        eids int[],
        primary key (level, last, id) include (ath)
    );
    
    insert into levels(level, first, last, ath, eids) values (1, start_node, start_node, '{}'::text[], '{}'::int[]);

    while exists (select 1 from levels l where l.level = depth) and depth <= max_depth loop
--        RAISE NOTICE '%: Path: %', depth, (select string_agg(array_to_string(cl.path, ','), ';  ') from levels cl where cl.level = depth);

        -- If the target node is one of the new paths, return the path
        if depth > 1 and exists (
          select 1 from levels q where q.level = depth and q.last = target_node
        ) then
          return query select * from levels q where q.level = depth and q.last = target_node;
          exit;
        end if;

        -- Insert neighbors into the next level if they haven't been visited
        insert into levels(level, first, last, ath, eids)
          select distinct depth + 1, cl.first, e.out, cl.ath || e.out, cl.eids || e.eid
          from levels cl
          join edges_both e on e.inp = cl.last and e.out <> all(cl.ath)
          where cl.level = depth and e.w >= minw;

        -- Clean up the current level
        delete from levels l where l.level = depth;

        depth := depth + 1;
    end loop;

    drop table if exists levels;		-- Cleanup
end;
$$;
