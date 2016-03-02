ROOT = `pwd`/..
LLVM_OCAML_LIB = $(ROOT)/build/lib/ocaml
LLVM_LIB = $(ROOT)/build/lib

LIB_FILES = llvm.cmxa,llvm_analysis.cmxa,llvm_target.cmxa,llvm_bitreader.cmxa,llvm_bitwriter.cmxa,llvm_scalar_opts.cmxa

OCAMLBUILD = ocamlbuild
OCAMLBUILD_OPT = -r \
	-I extraction \
	-I corehint \
	-I vellvm \
	-use-ocamlfind -pkg atdgen \
	-cflags -I,$(LLVM_OCAML_LIB) \
	-cflags -I,$(LLVM_LIB) \
	-cflags -g \
	-lflags -I,$(LLVM_OCAML_LIB) \
	-lflags -I,$(LLVM_LIB) \
	-lflags -cc,g++ \
	-lflags -cclib,-lLLVMSupport \
	-lflags -cclib,-lLLVMBitReader \
	-lflags -cclib,-lLLVMBitWriter \
	-lflags $(LIB_FILES)

MLS = extraction/FMapWeakList.ml extraction/FMapWeakList.mli \
	extraction/extraction_defs.ml extraction/extraction_defs.mli \
	extraction/Hints.ml extraction/Hints.mli \
	extraction/Validator.ml extraction/Validator.mli \
	extraction/Exprs.ml extraction/Exprs.mli \
	extraction/Infrules.ml extraction/Infrules.mli \
	extraction/Postcond.ml extraction/Postcond.mli \
	extraction/TODO.ml extraction/TODO.mli \
	corehint/coreHint_j.ml corehint/coreHint_j.mli \
	corehint/coreHint_t.ml corehint/coreHint_t.mli \
	coq2ml.ml convertUtil.ml domTreeUtil.ml convertHint.ml TODOCAML.ml \
	main.ml propagateHint.ml addInfrule.ml convertInfrule.ml tt.ml

all: main.native

main.native: $(MLS)
	$(OCAMLBUILD) $(OCAMLBUILD_OPT) main.native

corehint/coreHint_t.ml: corehint/coreHint.atd
	atdgen -t ./corehint/coreHint.atd
	atdgen -j ./corehint/coreHint.atd

corehint/coreHint_j.ml: corehint/coreHint.atd
	atdgen -t ./corehint/coreHint.atd
	atdgen -j ./corehint/coreHint.atd

clean:
	rm ./corehint/coreHint_j.mli
	rm ./corehint/coreHint_t.mli
	rm ./corehint/coreHint_j.ml
	rm ./corehint/coreHint_t.ml
	$(OCAMLBUILD) -clean
