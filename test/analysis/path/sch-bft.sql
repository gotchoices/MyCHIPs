-- Breadth First Traversal (BFT) using array
create or replace function find_target_via_bft(start_node text, target_node text)
returns text[] language plpgsql as $$
declare
    edge record;
    current node_path;
    queue node_path[]; 
begin
    queue := array[row(start_node, array[start_node])::node_path]; -- Initialize with start node and its path

    while array_length(queue, 1) > 0 loop
        current := queue[1];
        queue := queue[2:array_upper(queue, 1)]; 

        RAISE NOTICE 'Queue: %', queue;

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
create or replace function find_target_via_bft(start_node text, target_node text)
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
        select id, path into queue_id, current_path from queue order by id asc limit 1;
        current_node := current_path[array_upper(current_path, 1)];
        delete from queue where id = queue_id;

        RAISE NOTICE 'Current Path: %', current_path;
        RAISE NOTICE 'Next Node: %', current_node;

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
create or replace function find_target_via_bft(start_node text, target_node text)
returns table(path text[]) language plpgsql as $$
declare
    current_path text[];
    current_node text;
begin
    -- Create current and next level tables
    drop table if exists current_level;
    drop table if exists next_level;

    create temp table current_level(node text primary key, path text[]);
    create temp table next_level(node text primary key, path text[]);
    
    insert into current_level(node, path) values (start_node, array[start_node]);

    <<outer_loop>>
    while exists (select 1 from current_level) loop
        -- Process each node in the current level
        for current_node, current_path in (select cl.node, cl.path from current_level cl) loop
            RAISE NOTICE 'Current Path: %', current_path;

            -- Insert neighbors into the next level if they haven't been visited
            insert into next_level(node, path)
                select distinct node, array_append(current_path, node)
                from (
                    select out as node from edges where inp = current_node and out <> all(current_path)
                    union all
                    select inp as node from edges where out = current_node and inp <> all(current_path)
                ) as _
                on conflict do nothing;

            -- If the target node is one of the new paths, return the path
            if exists (select 1 from next_level q where q.node = target_node) then
                return query select q.path from next_level q where q.node = target_node;
                exit outer_loop;
            end if;

        end loop;

        -- Empty current level and swap next level into current
        delete from current_level;
        insert into current_level select * from next_level;
        delete from next_level;

    end loop outer_loop;

    -- Cleanup
    drop table if exists current_level;
    drop table if exists next_level;

    return query select null::text[] as path;  -- if target_node is not reached
end;
$$;
