#Build UML files
PUML="plantuml"

all: scaling.svg test-paths.svg act-network.svg \
	use-tally.svg seq-tally.svg seq-tally-close.svg state-tally.svg \
	use-chit.svg seq-chit-pmt.svg seq-chit-inv.svg state-chit.svg \
	use-route.svg seq-route.svg seq-route-man.svg seq-route-auto.svg state-route.svg \
	use-lift.svg seq-lift-prop.svg seq-lift-conf.svg seq-lift-ref.svg state-lift.svg state-ref.svg seq-ref-aux.svg \
	use-cons.svg seq-cons.svg state-conf.svg state-cons.svg \
	use-noise.svg seq-noise.svg state-noise.svg trade-seq.svg

%.png: %.puml common.puml style.puml
	${PUML} $<

%.svg: %.puml common.puml style.puml
	${PUML} -tsvg $<

clean:
	rm -f *.cmapx
