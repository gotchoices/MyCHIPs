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

lang:
	${WM} lang

defs:
	${WM} defs

init:
	${WM} init

parm:
	${WM} --no-make init

run:	#Production run-time
	${WM} ${WMPATH}/lib/run_time.wm[st]

dev:	#Development run-time
	${WM} ${WMPATH}/lib/run_time.wm[st] ${WMPATH}/lib/develop.wm[st]

sql:	objects text defs
	${WM} init -s >../lib/schema-1.sql

clean:	run
	${WM} ${WMPATH}/lib/run_time.wmi

schema:	objects clean text defs
	${WM} init -S ../lib/schema.json

commit:	schema
	${WM} -C

all: objects text defs init
