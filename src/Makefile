VS_VALIDATOR := $(wildcard validator/*.v)
VS_PROOFS    := $(filter-out $(wildcard extraction/*.v), $(filter-out $(wildcard validator/*.v), $(wildcard */*.v)))
VS_EXTRACTOR := $(wildcard extraction/*.v)
VS           := $(VS_VALIDATOR) $(VS_PROOFS) $(VS_EXTRACTOR)
IS           := $(sort $(subst /, , $(dir $(VS))))
COQLIBS      := -I ../lib/vellvm/src/Vellvm \
                -I ../lib/vellvm/src/Vellvm/ott \
                -I ../lib/vellvm/src/Vellvm/Dominators \
                -I ../lib/vellvm/lib/GraphBasics \
                -I ../lib/vellvm/lib/compcert-1.9 \
                -I ../lib/vellvm/lib/cpdtlib \
                -I ../lib/vellvm/lib/metalib-20090714 \
                -R ../lib/vellvm/lib/Coq-Equations-8.4/theories Equations \
                -I ../lib/vellvm/lib/Coq-Equations-8.4/src \
                $(addprefix -I ,$(IS)) \
                -impredicative-set
MAKECOQ=$(MAKE) -f Makefile.coq COQLIBS="$(COQLIBS)"

.PHONY: all theories clean

all: theories

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

theories: Makefile.coq
	+$(MAKECOQ)

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
