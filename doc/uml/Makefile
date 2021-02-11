#Build UML files
PUML="plantuml"

all: scaling.svg use-tally.svg use-chit.svg seq-tally.svg seq-tally-close.svg \
	seq-chit-pmt.svg seq-chit-inv.svg \
	state-tally.svg state-chit.svg

%.png: %.puml common.puml style.puml
	${PUML} $<

%.svg: %.puml common.puml style.puml
	${PUML} -tsvg $<

clean:
	rm -f *.cmapx
