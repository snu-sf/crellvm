COQMODULE     := LLVMBerry
COQDEFINITION := $(wildcard coq/exec/*.v coq/validator/*.v)
COQEXTRACT    := $(wildcard coq/extraction/*.v)
COQPROOF      := $(filter-out $(COQEXTRACT), $(filter-out $(COQDEFINITION), $(wildcard coq/*/*.v)))
COQTHEORIES   := $(COQDEFINITION) $(COQEXTRACT) $(COQPROOF)

JOBS=8
ROOT=`pwd`
LLVM_SRCDIR=${ROOT}/lib/llvm
LLVM_OBJDIR=${ROOT}/.build/llvm-obj
LLVM_LOCALDIR=${ROOT}/build

.PHONY: all init Makefile.coq llvm llvm-install lib definition extract exec proof test clean

all: exec proof

init:
	opam install menhir ott batteries biniou atdgen cppo easy-format ctypes coq.8.5.0~camlp4
	git checkout refactoring
	git clone git@github.com:snu-sf/simplberry-tests.git simplberry-tests
	git clone git@github.com:snu-sf/llvm.git lib/llvm
	cd lib/llvm; git checkout refactoring; git submodule init; git submodule update
	git clone git@github.com:snu-sf/paco.git lib/paco
	git clone git@github.com:snu-sf/sflib.git lib/sflib
	git clone git@github.com:snu-sf/vellvm-legacy.git lib/vellvm
	$(MAKE) -C lib/vellvm init

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
	./script/llvm-build.sh $(JOBS)
	./script/llvm-install.sh $(JOBS)

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
	rm -rf results-opt
	python ./simplberry-tests/test.py -e ./build/bin/opt -v ./ocaml_refact/main.native -r "-instcombine" -o -i "./simplberry-tests/inputs_full"
	python ./simplberry-tests/listfails.py -f results-opt
	python ./simplberry-tests/statistics.py -f results-opt -o

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
