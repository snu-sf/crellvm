COQMODULE     := Crellvm
COQDEF := $(wildcard coq/def/*.v)
COQEXTRACT    := $(wildcard coq/extract/*.v)
COQPROOF      := $(filter-out $(COQEXTRACT), $(filter-out $(COQDEF), $(wildcard coq/*/*.v)))
COQTHEORIES   := $(COQDEF) $(COQEXTRACT) $(COQPROOF)
PROOF_BUILD_DIR=.proof_build

JOBS=24
ROOT=`pwd`
LLVM_SRCDIR=${ROOT}/lib/llvm
LLVM_OBJDIR=${ROOT}/.build/llvm-obj

.PHONY: all init Makefile.coq opt llvm lib def extract exec proof test clean

all: llvm exec proof

quick: llvm exec-rsync proof-quick

init:
	opam install menhir ott.0.25 batteries biniou atdgen cppo easy-format ctypes coq.8.6
	git clone git@github.com:snu-sf/crellvm-tests.git crellvm-tests -b pldi2018-ae
	git clone git@github.com:snu-sf/crellvm-tests-parallel.git crellvm-tests/crellvm-tests-parallel
	git clone git@github.com:snu-sf/llvm.git lib/llvm
	git clone git@github.com:snu-sf/cereal.git lib/llvm/include/llvm/cereal
	git clone git@github.com:snu-sf/paco.git lib/paco
	git clone git@github.com:snu-sf/vellvm-legacy.git lib/vellvm
	$(MAKE) -C lib/vellvm init

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-R coq $(COQMODULE)"; \
   echo "-R lib/paco/src Paco"; \
   echo "-R lib/vellvm/src Vellvm"; \
   echo "-R lib/vellvm/lib/sflib sflib"; \
   echo "-R lib/vellvm/lib/metalib metalib"; \
   echo "-R lib/vellvm/lib/cpdtlib Cpdt"; \
   echo "-R lib/vellvm/lib/compcert-2.4 compcert"; \
   echo $(COQTHEORIES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

opt:
	cd .build/llvm-obj; cmake --build . -- opt -j$(JOBS)

llvm:
	./script/llvm-build.sh $(JOBS)

rsync-send:
	sh script/rsync-send.sh

rsync-receive:
	sh script/rsync-receive.sh

lib: lib/paco/src lib/vellvm
	$(MAKE) -C lib/paco/src
	$(MAKE) -C lib/vellvm

lib-quick: lib/paco/src lib/vellvm
	$(MAKE) -C lib/paco/src quick
	$(MAKE) -C lib/vellvm quick

def: Makefile.coq lib $(COQDEF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQDEF))

def-quick: Makefile.coq lib-quick $(COQDEF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQDEF))

extract: def $(COQEXTRACT)
	$(MAKE) -C lib/vellvm extract
	$(MAKE) -C coq/extract

exec: extract
	$(MAKE) -C ocaml

exec-rsync: rsync-send
	$(MAKE) -C $(PROOF_BUILD_DIR) extract
	$(MAKE) rsync-receive
	$(MAKE) -C ocaml

proof-rsync: rsync-send
	$(MAKE) -C $(PROOF_BUILD_DIR) proof

proof: def $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQPROOF))

proof-quick: def-quick $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQPROOF))

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

test:
	cd crellvm-tests; ./run-benchmark.sh

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
