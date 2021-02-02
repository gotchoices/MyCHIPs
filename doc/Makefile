#Build UML files
PUML="plantuml"

all: scaling.png use-chit.png use-tally.png state-tally.png state-chit.png

%.png: %.puml common.puml style.puml
	${PUML} $<

%.svg: %.puml common.puml style.puml
	${PUML} -tsvg $<
