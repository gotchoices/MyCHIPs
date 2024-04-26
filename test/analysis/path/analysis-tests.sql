@&#$#  -- keep from running
select count(*) from nodes limit 10 rows

delete from nodes;
delete from edges;
select * from nodes where name = 'n10001'
select * from edges where inp = 'n10001'

select * from find_target_table_via_bft('n3', 'n8');
select * from find_target_array_via_bft('n3', 'n8');
select * from find_target_multi_via_bft('n3', 'n8');
select * from find_target_multi_via_bfto('n4776', 'n2771', 0, 7);
select * from find_target_bidi_bft('n4776', 'n2771');
select * from find_target_multi_analy_bft('n3', 'n800', null);
select * from find_target_multi_analy_bft('n3', 'n800');

--delete from run_details;
--delete from histogram;
select * from run_details;
select * from histogram
select algorithm, round(avg_npaths, 2) as npaths, round(avg_level, 2) as level, round(avg_dcount, 2) as dcount, round(avg_qcount, 2) as qcount, found_count as found, run_count as runs
    from histogram where num_nodes = 10501

-- Scenario: 10k nodes, 30k edges
delete from nodes; delete from edges;
select * from random_graph(10000, 30000);
call run_bft_tests('uni', 500);

-- Scenario: 10k nodes, 70k edges
delete from nodes; delete from edges;
select * from random_graph(10000, 70000);
call run_bft_tests('uni', 500);

-- Scenario: 10.5k nodes, 120k edges
delete from nodes; delete from edges;
select * from random_graph(10501, 120100);
call run_bft_tests('uni', 500);

-- Scenario: 10k nodes, 70k edges + 500 supernodes w/ 100 edges each
select * from random_graph(10000, 70000);
select * from random_supernodes(500, 100, 10001);
call run_bft_tests('uni-5%super', 500);

-- Scenario: 10.5k nodes, 120k edges - 200 nodes clusters at 80% cluster chance
delete from nodes; delete from edges;
select * from random_clustered(10501, 120100, 200, 0.8);
call run_bft_tests('uni-200ncl@80%', 500);

-- Scenario: 10.5k nodes, 120k edges - 200 nodes clusters at 80% cluster chance - cluster search
delete from nodes; delete from edges;
select * from random_clustered(10501, 120100, 200, 0.8);
call run_bft_tests('uni-200ncl@80%-cs', 500, 200, 0.8);

-- Scenario: 10k nodes, 70k edges + 500 supernodes w/ 100 edges each - 200 nodes clusters at 80% cluster chance - cluster search
delete from nodes; delete from edges;
select * from random_clustered(10000, 70000, 200, 0.8);
select * from random_supernodes(500, 100, 10001);
call run_bft_tests('uni-200ncl@80%+5%sup-cs', 500, 200, 0.8);

-- Scenario: 10k nodes, 70k edges + 500 supernodes w/ 100 edges each - 200 nodes clusters at 80% cluster chance - cluster search - any balance
-- delete from histogram where algorithm = 'uni-200ncl@80%+5%sup-cs-ab';
-- delete from run_details where algorithm = 'uni-200ncl@80%+5%sup-cs-ab';
call run_bft_tests('uni-200ncl@80%+5%sup-cs-ab', 500, 200, 0.8);    -- temporarily changed to call: find_target_multi_analy_bft(source_node, target_node, null)
