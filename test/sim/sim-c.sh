#!/bin/bash
#Copyright MyCHIPs.org; See license in root of this package
# -----------------------------------------------------------------------------
#This is used by simulation containers as a startup script.
#It can also be executed by the running devel container to do other tasks.
#It should not typically be invoked directly.
tmpdir="/var/tmp/mychips"
command=${1:-spa}; shift			#Command not encoded
ofile="$tmpdir/$command"
#exec 1>$ofile.out 2>$ofile.err

pargs=()
while [[ $# -gt 0 ]]; do			#Decrypt command line arguments
  pargs+=("$(echo "$1" | base64 -d)")
  shift
done
#echo "pargs:${pargs[@]}"
set -- "${pargs[@]}"				#Restore positional arguments ($1..)
#echo "@:$@"

mydir="$(dirname $BASH_SOURCE)"			#Where this script is
appdir="$(realpath "$mydir/../..")"
#echo "mydir:$mydir appdir:$appdir" wsports:$wsports @:"$@"; #exit 0

if [[ ! -z $SITE ]]; then			#SITE is our site number 0..N
  export MYCHIPS_DBHOST="pg$SITE"		#Used by server to access postgres
  export MYCHIPS_AGENT="agent$(printf '%03d' $SITE)"	#Agent name length must be modulo 4
  export MYCHIPS_AGHOST="peer$SITE"
  export MYCHIPS_AGPORT="65430"
  
  if [[ ! -z $wsports ]]; then			#Only true when remote on devel called
    export MYCHIPS_USER_HOST="spa$SITE"		#values will be used by schema/parm.wmi
    export MYCHIPS_USER_PORT=$(expr $wsports + $SITE)
  fi
fi
#echo "command:$command PATH:$PATH NODE_DEBUG:$NODE_DEBUG wsports:$wsports args:$@"

function query {
  psql -h $MYCHIPS_DBHOST $dbname $admin -c "$@"
}

case $command in
  spa)		# Launch mychips with only SPA server capabilities
    { $appdir/bin/localcerts -b web && $appdir/bin/mychips.js -a "" "$@" ; } 1>$ofile.out 2>$ofile.err
    ;;

  peer)
    $appdir/bin/mychips.js -e 0 -i 0 -d 0 \
    	-a "${MYCHIPS_AGENT}@${MYCHIPS_AGHOST}:${MYCHIPS_AGPORT}" "$@" \
    	1>$ofile.out 2>$ofile.err
    ;;

  model)
    $appdir/test/sim/model "$@" 1>$ofile.out 2>$ofile.err
    ;;

  dbcheck)
#echo "DBCheck: pg:$MYCHIPS_DBHOST $MYCHIPS_DBPORT PATH:$PATH cwd:$(pwd) @:$@"
    if ! cd schema; then
      echo "Can't find db schema directory" >&2; exit 1
    fi
    lastfile=${tmpdir}/schema_build.$MYCHIPS_DBHOST
    dobuild=false
    if [ ! -f $lastfile -o "x$1" = "x-f" ]; then
      dobuild=true
    else
      news=$(find . -newer $lastfile |wc -l)
      if [ $news -gt 0 ]; then dobuild=true; fi
    fi
#echo "dobuild:$dobuild admin:$admin dbname:$dbname"; #exit 0

    if [[ $(psql -A -t -h $MYCHIPS_DBHOST template1 $admin -c "select * from pg_database where datname = '$dbname'" |wc -l) -lt 1 ]]; then
      echo -n "Full schema build on site $SITE: "
      make objects text defs init
      dobuild=false
      date >$lastfile
    fi

    if $dobuild; then
      echo -n "Incremental schema update on site $SITE: "
      make text objects
      date >$lastfile
    fi
    ;;

  parms)		#Re-initialize parameter table
    if ! cd schema; then
      echo "Can't find db schema directory" >&2; exit 1
    fi
    make parm
    ;;

  usercheck)
    newusers=${1:-$newusers}; shift
    maxuser="$(expr $newusers - 1 + 1000)"

    cd $appdir
    users="$(query "select * from mychips.users_v where ent_num > 1" -A -t |wc -l)"
    echo "Checking users ($users:$newusers) on site $SITE:"
    if [[ $users -lt $newusers ]]; then
#echo "N: $newusers $users $MYCHIPS_DBHOST"
      echo -n "  Adding $(expr $newusers - $users) users: "
      test/sample/randuser -n $(expr $newusers - $users)
    elif [[ $users -gt $newusers ]]; then
      echo -n "  Deleting any excess users: "
      query "delete from base.ent where ent_num > $maxuser"	#Trim to max number of users
    fi
    echo -n "  Clearing tallies: "
    query "delete from mychips.tallies; update mychips.users set _last_tally = 0;"

    ;;

  q) query "$@";;		#DB query

  backup)
    profile=${1:-backup}; shift
    backdir=$tmpdir/save/$profile; mkdir -p $backdir >/dev/null
    backfile=$backdir/$MYCHIPS_DBHOST.dump
    echo "Backup to: $backfile"
    pg_dump -d $dbname -U $admin -h $MYCHIPS_DBHOST >$backfile
    ;;

  restore)
    profile=${1:-backup}; shift
    backfile=$tmpdir/save/$profile/$MYCHIPS_DBHOST.dump
    echo "Restore from: $backfile"
    createdb -U $admin -h $MYCHIPS_DBHOST $dbname
    psql -d $dbname -U $admin -h $MYCHIPS_DBHOST -f $backfile
    ;;

  dropdb) dropdb -U $admin -h $MYCHIPS_DBHOST $dbname;;

  *) $command "$@";;	#Arbitrary shell command
    
esac
