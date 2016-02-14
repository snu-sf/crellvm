COQMODULE     := LLVMBerry
COQDEFINITION := $(wildcard src/validator/*.v)
COQEXTRACT    := $(wildcard src/extraction/*.v)
COQPROOF      := $(filter-out $(COQEXTRACT), $(filter-out $(COQDEFINITION), $(wildcard src/*/*.v)))
COQTHEORIES   := $(COQDEFINITION) $(COQEXTRACT) $(COQPROOF)

.PHONY: all vellvm

all: proof

init:
	git submodule init
	git submodule update
	$(MAKE) -C lib/vellvm init
	cd lib/llvm; git submodule init; git submodule update

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R src $(COQMODULE)"; \
   echo "-R lib/sflib sflib"; \
   echo "-R lib/paco/src Paco"; \
   echo "-R lib/vellvm/src Vellvm"; \
   echo "-R lib/vellvm/lib/metalib metalib"; \
   echo "-R lib/vellvm/lib/cpdtlib Cpdt"; \
   echo "-R lib/vellvm/lib/compcert-2.4 compcert"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

lib: lib/sflib lib/paco/src lib/vellvm
	$(MAKE) -C lib/sflib
	$(MAKE) -C lib/paco/src
	$(MAKE) -C lib/vellvm

definition: Makefile.coq lib $(COQDEFINITION)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQDEFINITION))

proof: definition $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQPROOF))

extract: definition $(COQEXTRACT)
	$(MAKE) -C lib/vellvm extract
	$(MAKE) -C src/extraction clean
	$(MAKE) -C src/extraction

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq