#Process schema files
WYSELIB = ~/share/devel/wyselib/schema
ifeq ("$(DBNAME)","")
  DBNAME = $(shell id -un)
endif

objects:
	wyseman --dbname=${DBNAME} ${WYSELIB}/*.wms ${WYSELIB}/base/*.wms *.wms

text:
	wyseman --dbname=${DBNAME} ${WYSELIB}/wylib.wmt ${WYSELIB}/base/*.wmt *.wmt

defs:
	wyseman --dbname=${DBNAME} ${WYSELIB}/base/*.wmd *.wmd

init:
	wyseman --dbname=${DBNAME} ${WYSELIB}/base/*.wmi *.wmi

sql:	objects text
	wyseman -s --dbname=${DBNAME} ${WYSELIB}/base/*.wmi *.wmi >../lib/schema-1.sql

all: objects text defs init
