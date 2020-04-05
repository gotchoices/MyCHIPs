#!/bin/bash
#Do any initialization of postgres that may be necessary.
#This is intended to be run inside a docker postgresql container.

configfile=/var/lib/postgresql/data/pgdata/postgresql.conf
if ! grep '^log_min_messages' $configfile; then
  echo "Configuring Postgres for logging notices"
  echo 'log_min_messages = notice' >>$configfile
  echo 'log_error_verbosity = terse' >>$configfile
fi

set -e
psql -v ON_ERROR_STOP=1 --username postgres --dbname postgres <<-EOSQL
    create role admin with login createdb superuser createrole;
EOSQL
