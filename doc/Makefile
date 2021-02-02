#Build UML files
PUML="plantuml"

all: state-tally.png state-chit.png scaling.png

%.png: %.puml common.puml style.puml
	${PUML} $<
