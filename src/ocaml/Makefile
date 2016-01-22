SIMPLBERRY_HOME = `pwd`/../..
LLVM_OCAML_LIB = $(SIMPLBERRY_HOME)/.local/lib/ocaml
LLVM_LIB = $(SIMPLBERRY_HOME)/.local/lib
VELLVM_LIB = $(SIMPLBERRY_HOME)/lib/vellvm/src/Extraction


LIB_FILES = llvm.cmxa,llvm_analysis.cmxa,llvm_target.cmxa,llvm_bitreader.cmxa,llvm_bitwriter.cmxa,llvm_scalar_opts.cmxa

OCAMLBUILD = ocamlbuild
OCAMLBUILD_OPT = -r \
	-I extraction \
	-I corehint \
	-I appliers \
	-I vellvm/src/Extraction \
	-use-ocamlfind -pkg atdgen \
	-cflags -I,$(LLVM_OCAML_LIB) \
	-cflags -I,$(LLVM_LIB) \
	-cflags -g\
	-lflags -I,$(LLVM_OCAML_LIB) \
	-lflags -I,$(LLVM_LIB) \
	-lflags -cc,g++\
	-lflags -cclib,-lLLVMSupport\
	-lflags -cclib,-lLLVMBitReader\
	-lflags -cclib,-lLLVMBitWriter\
	-lflags $(LIB_FILES)

MLS = extraction/FMapWeakList.ml extraction/FMapWeakList.mli\
	extraction/extraction_defs.ml extraction/extraction_defs.mli\
	extraction/decs.ml extraction/decs.mli\
	extraction/hints.ml extraction/hints.mli\
	extraction/syntax_ext.ml extraction/syntax_ext.mli\
	extraction/validator_aux.ml extraction/validator_aux.mli\
	extraction/validator.ml extraction/validator.mli\
	corehint/coreHint_j.ml corehint/coreHint_j.mli\
	corehint/coreHint_t.ml corehint/coreHint_t.mli\
	coq2ml.ml coreHintUtil.ml translateCoreHint.ml\
	main.ml utility.ml propagateHints.ml addInferenceHints.ml microHints.ml commandArg.ml tt.ml \
	appliers/removeMaydiffApplier.ml \
	appliers/addSubApplier.ml \
	appliers/addAssocApplier.ml


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
