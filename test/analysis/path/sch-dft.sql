-- HACK: node_path structure is work around for bug in pgsql involving nested arrays
--drop type if exists node_path;
--create or replace type node_path AS (
--    node text,
--    path text[]
--);

-- Version of Depth First Traversal (DFT) using array
create or replace function find_target_array_via_dft(start_node text, target_node text)
returns text[] language plpgsql as $$
declare
    edge record;
    current node_path;
    stack node_path[]; 
begin
    stack := array[row(start_node, array[start_node])::node_path]; -- Initialize with start node and its path

    while array_length(stack, 1) > 0 loop
        --RAISE NOTICE 'Stack: %', (select string_agg(array_to_string(path, ','), ';  ') from unnest(stack));

        current := stack[array_upper(stack, 1)];
        stack := stack[1:array_upper(stack, 1) - 1]; 

        for edge in (
            select out node from edges where inp = current.node and out <> all(current.path)
            union all
            select inp node from edges where out = current.node and inp <> all(current.path)
        )
        loop
            if edge.node = target_node then
                return current.path || edge.node;
            end if;
            
            stack := stack || array[row(edge.node, current.path || edge.node)::node_path];
        end loop;
    end loop;

    return null;
end;
$$;

-- Temp table version of DFT
create or replace function find_target_table_via_dft(start_node text, target_node text)
returns text[] language plpgsql as $$
declare
    edge record;
    current_path text[];
    current_node text;
    stack_id integer;
begin
    drop table if exists stack;
    drop sequence if exists stack_id_seq;
    create temp sequence stack_id_seq;
    create temp table stack(
        id integer primary key default nextval('stack_id_seq'),
        path text[]
    );
    insert into stack(path) values (array[start_node]);

    while exists (select 1 from stack) loop
        -- Pop the latest path from the stack using the primary key for efficiency
        select id, path, path[array_upper(path, 1)] into stack_id, current_path, current_node from stack order by id desc limit 1;
        delete from stack where id = stack_id;

        --RAISE NOTICE 'Path: %', current_path;

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

            -- Push the new path to the stack
            insert into stack(path) values (current_path || edge.node);
        end loop;
    end loop;

    -- Cleanup
    drop table if exists stack;
    drop sequence if exists stack_id_seq;

    return null;  -- if target_node is not reached
end;
$$;


-- Version which uses an insert statement at each level.  Returns ties at return level.
create or replace function find_target_multi_via_dft(start_node text, target_node text)
returns table(path text[]) language plpgsql as $$
declare
    current_path text[];
    current_node text;
    stack_id integer;
begin
    drop table if exists stack;
    drop sequence if exists stack_id_seq;
    create temporary sequence stack_id_seq;
    create temp table stack(
        id integer primary key default nextval('stack_id_seq'),
        node text, -- last node in path (for efficiency?)
        path text[]
    );
    insert into stack(node, path) values (start_node, array[start_node]);

    while exists (select 1 from stack) loop
        -- Pop the latest path from the stack using the primary key for efficiency
        select s.id, s.node, s.path into stack_id, current_node, current_path from stack s order by id desc limit 1;
        delete from stack where id = stack_id;

        --RAISE NOTICE 'Path: %', current_path;

        -- Insert all paths from the current node that have not been visited into the stack
        insert into stack(node, path)
            select node, array_append(current_path, node)
            from (
                select out as node from edges where inp = current_node and out <> all(current_path)
                union all
                select inp as node from edges where out = current_node and inp <> all(current_path)
            ) as _;

        -- If the target node is one of the new paths, return the path
        if exists (select 1 from stack s where s.node = target_node) then
            return query select s.path from stack s where s.node = target_node;
            exit;
        end if;
    end loop;

    -- Cleanup
    drop table if exists stack;
    drop sequence if exists stack_id_seq;

    return query select null::text[] as path;  -- if target_node is not reached
end;
$$;

