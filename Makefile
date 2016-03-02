COQMODULE     := LLVMBerry
COQDEFINITION := $(wildcard coq/exec/*.v coq/validator/*.v)
COQEXTRACT    := $(wildcard coq/extraction/*.v)
COQPROOF      := $(filter-out $(COQEXTRACT), $(filter-out $(COQDEFINITION), $(wildcard coq/*/*.v)))
COQTHEORIES   := $(COQDEFINITION) $(COQEXTRACT) $(COQPROOF)

ROOT=`pwd`
LLVM_SRCDIR=${ROOT}/lib/llvm
LLVM_OBJDIR=${ROOT}/.build/llvm-obj
LLVM_LOCALDIR=${ROOT}/build

.PHONY: all init Makefile.coq llvm llvm-install lib definition extract exec proof test clean

all: exec proof

init:
	opam install menhir ott batteries biniou atdgen cppo easy-format ctypes coq.8.5.0~camlp4

	rm -rf simplberry-tests
	rm -rf lib/llvm
	rm -rf lib/paco
	rm -rf lib/vellvm
	rm -rf .build
	rm -rf build

	git submodule init
	git submodule update
	$(MAKE) -C lib/vellvm init
	cd lib/llvm; git submodule init; git submodule update

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R coq $(COQMODULE)"; \
   echo "-R lib/sflib sflib"; \
   echo "-R lib/paco/src Paco"; \
   echo "-R lib/vellvm/src Vellvm"; \
   echo "-R lib/vellvm/lib/metalib metalib"; \
   echo "-R lib/vellvm/lib/cpdtlib Cpdt"; \
   echo "-R lib/vellvm/lib/compcert-2.4 compcert"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

llvm: lib/llvm
	./script/llvm-build.sh
	./script/llvm-install.sh

lib: lib/sflib lib/paco/src lib/vellvm
	$(MAKE) -C lib/sflib
	$(MAKE) -C lib/paco/src
	$(MAKE) -C lib/vellvm

definition: Makefile.coq lib $(COQDEFINITION)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQDEFINITION))

extract: definition $(COQEXTRACT)
	$(MAKE) -C lib/vellvm extract
	$(MAKE) -C coq/extraction

exec: extract
	$(MAKE) -C ocaml

# TODO: remove this after refactoring
extract_refact: definition
	$(MAKE) -C coq/extraction_new

refact: extract_refact
	$(MAKE) -C ocaml_refact

proof: definition $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQPROOF))

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

test:
	python ./simplberry-tests/test.py -e ./build/bin/opt -v ./ocaml/main.native -r "-instcombine" -o -f -i "./simplberry-tests/inputs_full"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
