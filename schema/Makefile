#Process schema files
DBUSER = 'admin'
WSL = $(shell wyselib-info |cut -f 1-2 -d ' ' |tr ' ' '/')
ifneq ("$(WSL)","")
  WYSELIB = $(WSL)/schema
else ifeq ("$(WYSELIB)","")
  WYSELIB = ../../wyselib/schema
endif
ifeq ("$(MYCHIPSDB)","")
  DBNAME="mychips"
else
  DBNAME="$(MYCHIPSDBDB)"
endif
OPT = -n ${DBNAME} -u ${DBUSER}

objects:
	wyseman ${OPT} config.tcl ${WYSELIB}/*.wms ${WYSELIB}/base/*.wms *.wms

text:
	wyseman ${OPT} ${WYSELIB}/wylib.wmt ${WYSELIB}/base/*.wmt *.wmt

defs:
	wyseman ${OPT} ${WYSELIB}/base/*.wmd *.wmd

init:
	wyseman ${OPT} ${WYSELIB}/base/*.wmi *.wmi

parm:
	wyseman ${OPT} *.wmi

sql:	objects text
	wyseman ${OPT} ${WYSELIB}/base/*.wmi *.wmi >../lib/schema-1.sql

all: objects text defs init
