#!/bin/bash
#Called by simnet script to execute via ssh on a remote or local simulation machine
#Not normally called directly by the user

#Common code
#-------------------------------------------------------------------------------
this="$(basename ${BASH_SOURCE})"
mypath="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )";	#echo "mypath:$mypath"
source $mypath/config
index="${SIMNET_INDEX}"

mychips="$mypath"
mysim=""
while [[ $path != / ]]; do				#Find first bin dir above me
  if find "$mychips" -maxdepth 1 -mindepth 1 -type d -name bin | grep -q .; then
    break
  fi
  mysim="$(basename $mychips)/${mysim}"			#Find simulation directory
  mychips="$(cd $mychips/.. && pwd)"
done

if [ "$(basename "$mychips")" != "mychips" ]; then
  echo "Can't determine mychips main directory"
  exit 1
fi
if ! cd ${mychips}; then
  echo "Can't find mychips main directory"
  exit 1
fi

export PATH=$PATH:"${mychips}/../node_modules/.bin"		#;echo "PATH:$PATH"

#echo "sim.x Args:$@"; exit
pargs=()
while [[ $# -gt 0 ]]; do
#  echo "arg:$1:"
  pargs+=("$(echo $1 | base64 --decode)")
  shift
done

set -- "${pargs[@]}"					#Restore positional arguments ($1..)
#for i in "$@"; do echo "sim.x arg:$i"; done;		exit 0

command="$1"
shift
echo -e "\n---->Host:$(hostname); $command"

#Check configuration (running on a slave machine)
#-------------------------------------------------------------------------------
function config {
#  echo Configuring; exit 0
  rpms=""						#Install any rpms we may need
  for pkg in postgresql-server postgresql-devel postgresql-pltcl postgresql-contrib ruby rubygem-pg rubygem-tk; do
    if ! rpm -qi $pkg >/dev/null; then
      rpms="${rpms} $pkg"
    fi
  done
  #echo "rpms:$rpms"
  if [ ! -z "$rpms" ]; then
    dnf install -y $rpms
  fi
  
  if [ ! -d /var/lib/pgsql/data/base ]; then		#Initialize PostgreSQL
    su -l postgres -c "initdb --locale=C"		#Might also use: eng_US.UTF-8
    systemctl enable postgresql
    systemctl start postgresql
  fi
  
  if [ "$(psql -A -t template1 postgres -c "select * from pg_roles where rolname = 'admin'" |wc -l)" -lt 1 ]; then
    su -l postgres -c 'createuser -d -s -r admin'	#Create our administrative user
  fi
}

#Kill any running services
#-------------------------------------------------------------------------------
function stop {
  mkdir -p $tmpdir
  if [ -f $tmpdir/pids ]; then				#Kill any running servers
    for p in $(cat $tmpdir/pids); do
      echo "  Killing old server pid: $p"
      kill $p 2>/dev/null
    done
    rm $tmpdir/pids; touch $tmpdir/pids
  fi
}
  
#Relaunch mychips server
#-------------------------------------------------------------------------------
function mychips {
#echo "peers DEBUG:$NODE_DEBUG args:$*"
  bin/mychips.js "$@" 2>$tmpdir/mychips.err &
  pid=$!
  echo "  MyCHIPs Server PID: $pid"
  echo $pid >>$tmpdir/pids		#Remember its Process ID for next time
}
    
#Agent simulation
#-------------------------------------------------------------------------------
function agents {
echo "agent args: $@"
  MYCHIPS_DDHOST="$public" test/sim/agent -m 2 "$@" 2>$tmpdir/agent2.err &
  pid=$!
  echo "  Agent Model PID: $pid"
  echo $pid >>$tmpdir/pids
}

#Log windows
#-------------------------------------------------------------------------------
function logs {
  file=combined.log;	if [[ ! -z $1 ]]; then file="$1"; fi
  base=0;		if [[ ! -z $2 ]]; then base="$2"; fi
  xoff=30; yoff=30
  
  geom="+$(expr $base + \( $index \* $xoff \))+$(expr $index \* $yoff)"
#echo "xterm index: $index geom:$geom"
  xterm -T "$(hostname): $file" -geometry "$geom" -e /bin/bash -l -c "tail -n 0 -f $tmpdir/$file" &
  pid=$!
  echo "  Terminal PID: $pid"
  echo $pid >>$tmpdir/pids
}

#Relaunch any services (running on a remote or local vm)
#-------------------------------------------------------------------------------
function start {
  stop
  logs agent2 0
  logs peer 600
  builddb
  mychips -s 0 -i 0
  agents "$@"
}

#Reconstruct the database if necessary
#-------------------------------------------------------------------------------
#if [[ $command == builddb ]]; then
function builddb {
#  echo "Build: $(pwd)"
  if ! cd schema; then
    echo "Can't find db schema directory"
    exit 1
  fi
  lastfile=${tmpdir}/last_schema_build
  dobuild=false
  if [ ! -f $lastfile ]; then
    dobuild=true
  else
    news=$(find . -newer $lastfile |wc -l)
    if [ $news -gt 0 ]; then
      dobuild=true
    fi
  fi
#echo "dobuild:$dobuild"

#No DB yet: let's build everything
  if [[ $(psql -A -t template1 $admin -c "select * from pg_database where datname = '$dbname'" |wc -l) -lt 1 ]]; then
    echo "Doing full build:"
    make objects text defs init
    dobuild=false
    date >$lastfile
  fi

  if $dobuild; then
    make objects parm
    date >$lastfile
  fi

  cd $mychips
  users="$(psql -A -t $dbname $admin -c "select * from mychips.users_v where ent_num > 1" |wc -l)"
  if [[ $users -lt $newusers ]]; then
    test/sample/randuser -n $(expr $newusers - $users)
  fi
}

#Initialize for a simulation run
#-------------------------------------------------------------------------------
function init {
  if [[ $1 == '-a' ]]; then
    newusers="$2"
    shift 2
  fi
  echo "Agents:$newusers"
  maxuser="$(expr $newusers - 1 + 1000)"
  psql $dbname $admin -c 'delete from mychips.tallies'
  psql $dbname $admin -c "delete from base.ent where ent_num > $maxuser"
}

#Query the SQL database
#-------------------------------------------------------------------------------
function q {
  query="$1"
  shift
  psql $dbname $admin -c "$query" "$@"
}

if [[ -z $command ]]; then
  command="start"
fi

$command "$@"
