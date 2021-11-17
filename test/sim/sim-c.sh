#!/bin/bash
#Copyright MyCHIPs.org; See license in root of this package
# -----------------------------------------------------------------------------
#Called within a container to launch various server processes in simulation mode
#Normally called from simdock--not directly by the user
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

mydir="$(dirname $BASH_SOURCE)"		#Where this script is
appdir="$(realpath "$mydir/../..")"
#echo "mydir:$mydir appdir:$appdir" @:"$@"; #exit 0

if [[ -L "$appdir/../node_modules/.bin/wyseman" ]]; then	#Find location of node binaries
  nbdir="$appdir/../node_modules/.bin"
elif [[ -L "$appdir/node_modules/.bin/wyseman" ]]; then
  nbdir="$appdir/node_modules/.bin"
else
  echo "Can't find path for development commands (run npm install?)"
  exit 1
fi

IFS=: read -r -a patha <<< "$PATH"			#Put it in our path
if [[ ! -z "$nbdir" && ! "${patha[@]}" =~ "$nbdir" ]]; then
  export PATH="${PATH}:$nbdir"
fi
if [[ ! -z $SITE ]]; then			#SITE is our site number 0..N
  export MYCHIPS_USER_HOST="spa$SITE"
  export MYCHIPS_DBHOST="pg$SITE"
  export MYCHIPS_PEER_HOST="peer$SITE"		#values will be used by schema/parm.wmi
  export MYCHIPS_PEER_AGENT="agent$SITE"
  export MYCHIPS_USER_PORT=$(expr $wsports + $SITE)
fi
#echo "command:$command PATH:$PATH NODE_DEBUG:$NODE_DEBUG wsports:$wsports args:$@"

function query {
  psql -h $MYCHIPS_DBHOST $dbname $admin -c "$@"
}

case $command in
  spa)
    $appdir/bin/localcerts -b spa && $appdir/bin/mychips.js -p 0 "$@" 1>$ofile.out 2>$ofile.err
    ;;

  peer)
    $appdir/bin/localcerts -b peer && $appdir/bin/mychips.js -s 0 -i 0 -d 0 "$@" 1>$ofile.out 2>$ofile.err
    ;;

  agent)
    $appdir/test/sim/agent "$@" 1>$ofile.out 2>$ofile.err
    ;;

  dbcheck)
#    echo "DBCheck: pg:$MYCHIPS_DBHOST PATH:$PATH cwd:$(pwd) @:$@"
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
      echo "Doing full build:"
      make objects text defs init
      dobuild=false
      date >$lastfile
    fi

    if $dobuild; then
      make objects
      date >$lastfile
    fi
    make parm
    ;;

  usercheck)
    newusers=${1:-$newusers}; shift
    maxuser="$(expr $newusers - 1 + 1000)"
#echo "usercheck appdir:$appdir newusers:$newusers"; #exit 0
    query "delete from mychips.tallies"
    query "delete from base.ent where ent_num > 1000 and not exists (select * from mychips.users where user_ent = id)"	#Delete any foreign peers
    query "delete from base.ent where ent_num > $maxuser"	#Trim to max number of agents

    cd $appdir
    users="$(query "select * from mychips.users_v where ent_num > 1" -A -t |wc -l)"
    if [[ $users -lt $newusers ]]; then
      test/sample/randuser -n $(expr $newusers - $users)
    fi
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
