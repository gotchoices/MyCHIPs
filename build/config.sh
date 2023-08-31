#Source this file to set environment variables for docker-compose

if [[ "$1" =~ ^dev(elop)?$ ]]; then
  export MYCHIPS_ROOTDIR="$(git rev-parse --show-toplevel)"
  export MYCHIPS_ROOTNAME="$(basename $MYCHIPS_ROOTDIR)"
  export MYCHIPS_DEVDIR=/usr/local/devel
  export MYCHIPS_DEBUG=debug
else
  export MYCHIPS_DEBUG=warn
fi

export MYCHIPS_HOST=mychips0
export MYCHIPS_DBHOST=postgres0
export MYCHIPS_UIPORT=1024
export MYCHIPS_WSPORT=1025
