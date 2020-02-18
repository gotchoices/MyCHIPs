#!/bin/bash
#Do any initialization of postgres that may be necessary.
#This is intended to be run inside a docker postgresql container.

set -e
psql -v ON_ERROR_STOP=1 --username postgres --dbname postgres <<-EOSQL
    create role admin with login createdb superuser createrole;
EOSQL
