COQMODULE     := Crellvm
COQDEF := $(wildcard coq/def/*.v)
COQEXTRACT    := $(wildcard coq/extract/*.v)
COQPROOF      := $(filter-out $(COQEXTRACT), $(filter-out $(COQDEF), $(wildcard coq/*/*.v)))
COQTHEORIES   := $(COQDEF) $(COQEXTRACT) $(COQPROOF)
PROOF_BUILD_DIR=.build-proof

JOBS=24
ROOT=`pwd`
LLVM_SRCDIR=${ROOT}/lib/llvm
LLVM_OBJDIR=${ROOT}/.build/llvm-obj

.PHONY: all init Makefile.coq opt llvm lib def extract exec proof test clean

all: llvm exec proof

quick: llvm exec proof-quick

init:
	opam install -y menhir ott.0.25 batteries biniou atdgen cppo easy-format ctypes coq.8.6 # Ott 0.25 is required for avoiding a strange build error, and Coq 8.6 is for building CompCert 2.4.
	git clone https://github.com/snu-sf/crellvm-llvm.git lib/llvm
	git clone https://github.com/snu-sf/crellvm-vellvm.git lib/vellvm
	git clone https://github.com/snu-sf/cereal.git lib/llvm/include/llvm/cereal
	git clone https://github.com/snu-sf/paco.git lib/paco
	$(MAKE) -C lib/vellvm init

update:
	git -C lib/llvm pull
	git -C lib/vellvm pull
	git -C lib/llvm/include/llvm/cereal pull
	git -C lib/paco pull

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
	$(MAKE) -C lib/vellvm src/Vellvm/syntax_base.v
	$(MAKE) -C lib/vellvm src/Vellvm/typing_rules.v
	sh script/rsync-send.sh

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

exec: rsync-send
	$(MAKE) -C $(PROOF_BUILD_DIR) extract
	sh script/rsync-receive.sh
	$(MAKE) -C ocaml

exec-rsync: exec

proof: rsync-send
	$(MAKE) -C $(PROOF_BUILD_DIR) proof-inner

proof-inner: def $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQPROOF))

proof-quick: def-quick $(COQPROOF)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vio,$(COQPROOF))

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

%.vio: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

test-init:
	git clone https://github.com/snu-sf/crellvm-tests.git crellvm-tests -b pldi2018-ae
	git clone https://github.com/snu-sf/crellvm-tests-parallel.git crellvm-tests/crellvm-tests-parallel

test-update:
	git -C crellvm-tests pull
	git -C crellvm-tests/crellvm-tests/parallel pull

test:
	cd crellvm-tests; ./run-benchmark.sh

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
