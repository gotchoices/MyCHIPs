#Process schema files
DBUSER = 'admin'		#Has permissions to create/destroy DB objects
DBNAME='mychips'

WMPATH = $(shell wyseman-info path)
ifeq ("$(WMPATH)","")
  WMPATH = ../node_modules/wyseman
endif

WSL = $(shell wyselib-info path)
ifneq ("$(WSL)","")
  WYSELIB = $(WSL)/schema
else ifeq ("$(WYSELIB)","")
  WYSELIB = ../node_modules/wyselib/schema
endif

ifneq ("$(MYCHIPS_DBNAME)","")
  DBNAME = "$(MYCHIPS_DBNAME)"
endif
OPT := --user=$(DBUSER) --dbname=$(DBNAME)
ifneq ("$(MYCHIPS_DBHOST)","")
  OPT := $(OPT) --host=$(MYCHIPS_DBHOST)
endif
ifneq ("$(MYCHIPS_DBPORT)","")
  OPT := $(OPT) --port=$(MYCHIPS_DBPORT)
endif

objects:
	wyseman ${OPT} config.tcl ${WYSELIB}/*.wms ${WYSELIB}/base/*.wms *.wms

text:
	wyseman ${OPT} ${WYSELIB}/wylib.wmt ${WYSELIB}/base/*.wmt *.wmt

defs:
	wyseman ${OPT} ${WYSELIB}/base/*.wmd ${WYSELIB}/*.wmd *.wmd

init:
	wyseman ${OPT} ${WYSELIB}/base/*.wmi *.wmi

parm:
	wyseman ${OPT} *.wmi

run:
	wyseman ${OPT} ${WMPATH}/lib/run_time.wms

sql:	objects text defs
	wyseman ${OPT} -s ${WYSELIB}/base/*.wmi *.wmi >../lib/schema-1.sql

all: objects text defs init
