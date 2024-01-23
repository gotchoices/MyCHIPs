#Build UML files
PUML="plantuml"

all: scaling.svg test-paths.svg act-network.svg seq-model.svg \
	use-tally.svg seq-tally.svg seq-tally-close.svg state-tally-simp.svg state-tally.svg \
	use-chit.svg seq-chit-pmt.svg seq-chit-inv.svg state-chit.svg \
	use-route.svg seq-lift-pay.svg seq-lift-relay.svg state-lift.svg \
	use-cons.svg seq-cons.svg state-conf.svg state-cons.svg \
	use-noise.svg seq-noise.svg state-noise.svg trade-seq.svg

%.png: %.puml common.puml style.puml
	${PUML} $<

%.svg: %.puml common.puml style.puml
	${PUML} -tsvg $<

clean:
	rm -f *.cmapx
