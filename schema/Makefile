#Process schema files
ifeq ("$(WYSELIB)","")
  WYSELIB = ../node_modules/wyselib/schema
  DBUSER = 'admin'
endif
ifeq ("$(MYCHIPSDB)","")
  DBNAME="mychips"
else
  DBNAME="$(MYCHIPSDBDB)"
endif

objects:
	wyseman --dbname=${DBNAME} --user=${DBUSER} ${WYSELIB}/*.wms ${WYSELIB}/base/*.wms *.wms

text:
	wyseman --dbname=${DBNAME} --user=${DBUSER} ${WYSELIB}/wylib.wmt ${WYSELIB}/base/*.wmt *.wmt

defs:
	wyseman --dbname=${DBNAME} --user=${DBUSER} ${WYSELIB}/base/*.wmd *.wmd

init:
	wyseman --dbname=${DBNAME} --user=${DBUSER} ${WYSELIB}/base/*.wmi *.wmi

sql:	objects text
	wyseman -s --dbname=${DBNAME} --user=${DBUSER} ${WYSELIB}/base/*.wmi *.wmi >../lib/schema-1.sql

all: objects text defs init
