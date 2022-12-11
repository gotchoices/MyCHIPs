#Process schema files
#Sources resolve to definitions in ./Wyseman.conf
WMPATH = $(shell npm exec wyseman-info path)
ifeq ("$(WMPATH)","")
  WMPATH = ../node_modules/wyseman
endif
WM=npm exec wyseman --

objects:
	${WM} objects

text:
	${WM} text

defs:
	${WM} defs

init:
	${WM} init

parm:
	${WM} --no-make init

run:
	${WM} ${WMPATH}/lib/run_time.wm*

sql:	objects text defs
	${WM} init -s >../lib/schema-1.sql

schema:	objects text defs
	${WM} init -S ../lib/schema.json

commit:	schema
	${WM} -C

all: objects text defs init
