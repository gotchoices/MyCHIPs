#!/bin/env ruby

require 'pg'

db = PG.connect(dbname:'kyle', user:'kyle')

res = db.exec 'select * from pg_database'

puts res.fields
res.clear

#res.each {|row|
#    printf("%s:%s:%s:%s:\n", row['schemaname'], row['viewname'], row['viewowner'], row['pg_roles'])
#}

db.close if db
