-- ANALYZING optimized BFT
create or replace function find_target_multi_analy_bft(start_node text, target_node text, minw integer default 0, max_depth integer default 6)
returns table (
  id integer,
  level integer,
  first text,
  last text,
  ath text[],
  eids int[],
  dcount int,   -- distinct node count
  qcount int    -- total query count (including re-passthroughs)
) language plpgsql as $$
  declare
    depth int := 1;
    qcount int := 0;
    icount int := 0;
    found boolean := false;
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
    drop table if exists distinctNodes;
    create temp table distinctNodes (
        id text,
        primary key (id)
    );
    
    insert into levels(level, first, last, ath, eids) values (1, start_node, start_node, '{}'::text[], '{}'::int[]);

    while exists (select 1 from levels l where l.level = depth) and depth <= max_depth loop
        RAISE NOTICE '%: Path: %', depth, (select string_agg(cl.first || ',' || array_to_string(cl.ath, ','), ';  ') from levels cl where cl.level = depth);

        -- At each level, will pass through distinct set of parent nodes - approximate this
        with recursive lineage as (
                select 
                    unnest(l.ath) as ancestor_id,
                    generate_subscripts(l.ath, 1) as level
                from levels l where l.level = depth - 1 -- skip deepest because deepest represents peer knowlege, not visitation
            ),
            eachlevel as (
                select 
                    l.level,
                    count(distinct l.ancestor_id) as level_count
                from lineage l
                group by l.level
                order by l.level
            )
            select coalesce(sum(level_count), 0) into icount from eachlevel;
        qcount := qcount + icount;

        -- If the target node is one of the new paths, return the path
        if depth > 1 and exists (
          select 1 from levels q where q.level = depth and q.last = target_node
        ) then
            return query select *, (select count(*)::int from distinctNodes) dcount, qcount 
                from levels q where q.level = depth and q.last = target_node;
            found := true;
            exit;
        end if;

        -- Insert neighbors into the next level if they haven't been visited
        insert into levels(level, first, last, ath, eids)
            select distinct depth + 1, cl.first, e.out, cl.ath || e.out, cl.eids || e.eid
                from levels cl
                join edges_both e on e.inp = cl.last and e.out <> all(cl.ath)
                where cl.level = depth and (minw is null or e.w >= minw);

        -- Insert level below into distinctNodes but only if not already there
        insert into distinctNodes (id)
            select distinct cl.last
                from levels cl
                where cl.level = depth - 1  -- depth = peer knowlege, not visitation
                on conflict do nothing;

        -- Clean up one level below current level
        delete from levels l where l.level = depth - 1;

        depth := depth + 1;
    end loop;

    drop table if exists levels;		-- Cleanup
    -- Return dummy row if no path is found
    if not found then
        return query select null::int, null::int, null, null, null::text[], null::int[], (select count(*)::int from distinctNodes) dcount, qcount;
    end if;
end;
$$;

-- drop table if exists histogram;
create table histogram (
    num_nodes int not null,
    num_edges int not null,
    algorithm text not null,
    avg_npaths numeric null,
    avg_level numeric null,
    avg_dcount numeric null,
    avg_qcount numeric null,
    found_count int not null,
    run_count int not null,
    primary key (num_nodes, num_edges, algorithm)
);

-- drop table if exists run_details;
create table run_details (
    run_id serial not null primary key,
    num_nodes int not null,
    num_edges int not null,
    algorithm text not null,
    source_node text not null,
    target_node text not null,
    npaths int not null,
    level int null,
    dcount int null,
    qcount int null
);

create or replace procedure run_bft_tests(
    algorithm_name text,
    total_runs int = 500, 
    cluster_size int = 0, 
    cluster_prob float = 0
)
language plpgsql
as $$
declare
    source_node text;
    source_idx int;
    target_node text;
    target_idx int;
    result record;
    total_nodes int;
    total_edges int;
begin
    select count(*) into total_nodes from nodes;
    select count(*) into total_edges from edges;

    for i in 1..total_runs loop
        -- Randomly select source and target nodes
        source_idx := trunc(random() * (total_nodes - 1) + 1);
        source_node := 'n' || source_idx::text;
        target_node := source_node;

        if random() < cluster_prob then -- Connect to a node within the same cluster?
            while source_node = target_node loop
                -- Randomly select output within the same cluster
                target_idx := source_idx + floor(random() * cluster_size) - floor(cluster_size / 2);
                if target_idx < 0 then
                    target_idx := 0;
                elsif target_idx >= total_nodes then
                    target_idx := total_nodes - 1;
                end if;
                select name into target_node from nodes offset target_idx limit 1;
            end loop;
            else  -- Connect to a random node
            while source_node = target_node loop
                -- Randomly select output from the entire set of nodes
                select name into target_node from nodes offset floor(random() * total_nodes) limit 1;
            end loop;
        end if;

        --RAISE NOTICE '% -> %', source_node, target_node;

        -- Call search function and capture the result
        select coalesce(count(id), 0) npaths, level, dcount, qcount into result 
            from find_target_multi_analy_bft(source_node, target_node, null)
            group by level, dcount, qcount;

        --RAISE NOTICE '  nodes: %  edges: %  alg: %  s: %  t: %  npaths: %  level: %  dcount: %  qcount: %', total_nodes, total_edges, algorithm_name, source_node, target_node, result.npaths, result.level, result.dcount, result.qcount;

        -- Insert into run details
        insert into run_details (num_nodes, num_edges, algorithm, source_node, target_node, npaths, level, dcount, qcount)
            values (total_nodes, total_edges, algorithm_name, source_node, target_node, result.npaths, result.level, result.dcount, result.qcount);

        -- Update histogram stats
        update histogram
            set 
                avg_npaths = case when result.npaths > 0 then coalesce((avg_npaths * run_count + result.npaths) / (run_count + 1), result.npaths) else avg_npaths end,
                avg_level = case when result.npaths > 0 then coalesce((avg_level * found_count + result.level) / (found_count + 1), result.level) else avg_level end,
                avg_dcount = case when result.npaths > 0 then coalesce((avg_dcount * found_count + result.dcount) / (found_count + 1), result.dcount) else avg_dcount end,
                avg_qcount = case when result.npaths > 0 then coalesce((avg_qcount * found_count + result.qcount) / (found_count + 1), result.qcount) else avg_qcount end,
                found_count = found_count + case when result.npaths > 0 then 1 else 0 end,
                run_count = run_count + 1
            where num_nodes = total_nodes and num_edges = total_edges and algorithm = algorithm_name;

        -- Insert into histogram if not exists
        if not found then
            insert into histogram (num_nodes, num_edges, algorithm, avg_npaths, avg_level, avg_dcount, avg_qcount, found_count, run_count)
                values (total_nodes, total_edges, algorithm_name, 
                    case when result.npaths > 0 then result.npaths else null end, 
                    case when result.npaths > 0 then result.level else null end, 
                    case when result.npaths > 0 then result.dcount else null end, 
                    case when result.npaths > 0 then result.qcount else null end,
                    case when result.npaths > 0 then 1 else 0 end, 
                    1);
        end if;

        -- Commit transaction
        --commit;
    end loop;
end;
$$;

