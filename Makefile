.PHONY: submodules validator all llvm vellvm proof test

ROOT=`pwd`
LLVM_SRCDIR=$ROOT/lib/llvm
LLVM_OBJDIR=$ROOT/.build/llvm-obj
LLVM_LOCALDIR=${ROOT}/build

# all : builds all target, but no testing
all : submodules llvm llvm-install vellvm validator validator-ocaml

submodules :
	opam install menhir ott batteries biniou atdgen cppo easy-format ctypes
	rm -rf lib/llvm
	rm -rf lib/paco
	rm -rf lib/vellvm
	./script/load-submodules.sh

# llvm : compiles llvm
llvm:
	./script/build-llvm.sh

llvm-install:
	./script/install-llvm.sh

vellvm:
	./script/build-vellvm.sh

# validator : compiles validators (in src/ and src/ocaml, without proof). This is the default target.
validator:
	$(MAKE) -C ./src/ exec	 # This compiles validator codes of coq

validator-ocaml:
	$(MAKE) -C ./src/ocaml/  # This compiles validator codes of ocaml


# proof : compiles proof
proof:
	$(MAKE) -C ./src/ theories

# test : calls simplberry-test/run.py
test:
	
