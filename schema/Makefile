#Process schema files
WYSELIB = ~/share/devel/wyselib/schema
DBNAME = $(shell id -un)

all: objects text defs init

objects:
	wyseman --dbname=${DBNAME} ${WYSELIB}/*.wms ${WYSELIB}/base/*.wms *.wms

text:
	wyseman --dbname=${DBNAME} ${WYSELIB}/wylib.wmt ${WYSELIB}/base/*.wmt *.wmt

defs:
	wyseman --dbname=${DBNAME} ${WYSELIB}/base/*.wmd *.wmd

init:
	wyseman --dbname=${DBNAME} ${WYSELIB}/base/*.wmi *.wmi

sql:
	wyseman -s --dbname=${DBNAME} ${WYSELIB}/base/*.wmi *.wmi >../lib/schema-1.sql
