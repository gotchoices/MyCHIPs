#Build UML files
PUML="plantuml"

all: state-tally.png state-chit.png

%.png: %.puml common.puml
	${PUML} $<
