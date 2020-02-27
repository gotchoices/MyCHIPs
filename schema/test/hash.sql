
with example(col) as (
values 
    ('{"cc": 1, "ab": 2, "a": 3, "aa": 4, "b": 5, "abc": 6, "z":7, "AB":8}'::jsonb)
    )
    
    select col::text, sha256(col::text::bytea)
    from example
