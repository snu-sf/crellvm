COQMODULE     := LLVMBerry
COQDEF := $(wildcard coq/def/*.v)
COQEXTRACT    := $(wildcard coq/extract/*.v)
COQPROOF      := $(filter-out $(COQEXTRACT), $(filter-out $(COQDEF), $(wildcard coq/*/*.v)))
COQTHEORIES   := $(COQDEF) $(COQEXTRACT) $(COQPROOF)

JOBS=24
ROOT=`pwd`
LLVM_SRCDIR=${ROOT}/lib/llvm
LLVM_OBJDIR=${ROOT}/.build/llvm-obj

.PHONY: all init Makefile.coq opt llvm lib def extract exec proof test clean

all: exec proof

quick: exec-quick proof-quick

init:
	opam install menhir ott batteries biniou atdgen cppo easy-format ctypes coq.8.5.2~camlp4
	git clone git@github.com:snu-sf/simplberry-tests.git simplberry-tests
	git clone git@github.com:snu-sf/llvm.git lib/llvm
	git clone git@github.com:snu-sf/cereal.git lib/llvm/include/llvm/cereal
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

opt:
	cd .build/llvm-obj; cmake --build . -- opt -j$(JOBS)

llvm:
	./script/llvm-build.sh $(JOBS)

lib: lib/sflib lib/paco/src lib/vellvm
	$(MAKE) -C lib/sflib
	$(MAKE) -C lib/paco/src
	$(MAKE) -C lib/vellvm

lib-quick: lib/sflib lib/paco/src lib/vellvm
	$(MAKE) -C lib/sflib quick
	$(MAKE) -C lib/paco/src quick
	$(MAKE) -C lib/vellvm quick

def: Makefile.coq lib $(COQDEF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQDEF))

def-quick: Makefile.coq lib-quick $(COQDEF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQDEF)) quick

extract: def $(COQEXTRACT)
	$(MAKE) -C lib/vellvm extract
	$(MAKE) -C coq/extract

extract-quick: definition-quick $(COQEXTRACT)
	$(MAKE) -C lib/vellvm extract-quick
	$(MAKE) -C coq/extraction quick

exec: extract
	$(MAKE) -C ocaml

exec-quick: extract-quick
	$(MAKE) -C ocaml

proof: def $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQPROOF))

proof-quick: definition-quick $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQPROOF)) quick

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@" quick

test:
	rm -rf results-opt
	python ./simplberry-tests/test.py -e ./.build/llvm-obj/bin/opt -v ./ocaml/main.native -r "-O2" -o -i "./simplberry-tests/inputs_full"
	python ./simplberry-tests/listfails.py -f results-opt
	python ./simplberry-tests/statistics.py -f results-opt -o

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
