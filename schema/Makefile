#Process schema files
#Sources resolve to definitions in ./Wyseman.conf
WMPATH = $(shell wyseman-info path)
ifeq ("$(WMPATH)","")
  WMPATH = ../node_modules/wyseman
endif

objects:
	wyseman objects

text:
	wyseman text

defs:
	wyseman defs

init:
	wyseman init

parm:
	wyseman --no-make init

run:
	wyseman ${WMPATH}/lib/run_time.wms

sql:	objects text defs
	wyseman init -s >../lib/schema-1.sql

schema:	objects text defs
	wyseman init -S ../lib/schema.json

all: objects text defs init
