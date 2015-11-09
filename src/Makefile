VS_VALIDATOR := $(wildcard validator/*.v)
VS_PROOFS    := $(filter-out $(wildcard extraction/*.v), $(filter-out $(wildcard validator/*.v), $(wildcard */*.v)))
VS_EXTRACTOR := $(wildcard extraction/*.v)
VS_TEMP      := lib/my_gvar_dec.v lib/basic_const_inject.v
VS           := $(VS_VALIDATOR) $(VS_PROOFS) $(VS_EXTRACTOR)
IS           := $(sort $(subst /, , $(dir $(VS))))
COQLIBS      := -I ../lib/vellvm/src/Vellvm \
                -I ../lib/vellvm/src/Vellvm/Dominators \
                -I ../lib/vellvm/src/Extraction \
                -I ../lib/vellvm/lib/GraphBasics \
                -I ../lib/vellvm/lib/compcert-2.4/backend/ \
                -I ../lib/vellvm/lib/compcert-2.4/common/ \
                -I ../lib/vellvm/lib/compcert-2.4/flocq/Appli/ \
                -I ../lib/vellvm/lib/compcert-2.4/flocq/Calc/ \
                -I ../lib/vellvm/lib/compcert-2.4/flocq/Core/ \
                -I ../lib/vellvm/lib/compcert-2.4/flocq/Prop \
                -I ../lib/vellvm/lib/compcert-2.4/ia32/ \
                -I ../lib/vellvm/lib/compcert-2.4/lib/ \
                -I ../lib/vellvm/lib/compcert-2.4/old/ \
                -I ../lib/vellvm/lib/cpdtlib \
                -I ../lib/vellvm/lib/metalib-20090714 \
                $(addprefix -I ,$(IS))
MAKECOQ=$(MAKE) -f Makefile.coq COQLIBS="$(COQLIBS)"
MAKECOQCORE=$(MAKE) -f Makefile.exec.coq COQLIBS="$(COQLIBS)"

.PHONY: all theories clean

all: theories

exec: theories_exec

Makefile.coq: Makefile $(VS)
	coq_makefile $(VS) -o Makefile.coq

Makefile.exec.coq: Makefile $(VS_VALIDATOR) $(VS_EXTRACTOR) $(VS_TEMP)
	coq_makefile $(VS_VALIDATOR) $(VS_EXTRACTOR) $(VS_TEMP) -o Makefile.exec.coq

theories: Makefile.coq
	+$(MAKECOQ)

theories_exec: Makefile.exec.coq
	+$(MAKECOQCORE)
	mv *.ml *.mli extraction

cleanexec:
	$(MAKE) -f Makefile.exec.coq clean
	rm -f Makefile.exec.coq

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
