SIMPLBERRY_HOME = `pwd`/../..
LLVM_OCAML_LIB = $(SIMPLBERRY_HOME)/.local/lib/ocaml
LLVM_LIB = $(SIMPLBERRY_HOME)/.local/lib
VELLVM_LIB = $(SIMPLBERRY_HOME)/lib/vellvm/src/Extraction


LIB_FILES = llvm.cmxa,llvm_analysis.cmxa,llvm_target.cmxa,llvm_bitreader.cmxa,llvm_bitwriter.cmxa,llvm_scalar_opts.cmxa

OCAMLBUILD = ocamlbuild
OCAMLBUILD_OPT = -r \
	-I extraction \
	-I hintparser \
	-I appliers \
	-I vellvm/src/Extraction \
	-use-ocamlfind -pkg atdgen \
	-cflags -I,$(LLVM_OCAML_LIB) \
	-cflags -g\
	-lflags -I,$(LLVM_OCAML_LIB) \
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
	hintparser/hintParser_j.ml hintparser/hintParser_j.mli\
	hintparser/hintParser_t.ml hintparser/hintParser_t.mli\
	coq2ml.ml printHints.ml translateHints.ml\
	main.ml utility.ml propagateHints.ml addInferenceHints.ml microHints.ml tt.ml \
	appliers/cmdPropagateApplier.ml \
	appliers/addAssocApplier.ml


main.native: $(MLS)
	$(OCAMLBUILD) $(OCAMLBUILD_OPT) main.native

hintparser/hintParser_t.ml: hintparser/hintParser.atd
	atdgen -t ./hintparser/hintParser.atd
	atdgen -j ./hintparser/hintParser.atd
        
hintparser/hintParser_j.ml: hintparser/hintParser.atd
	atdgen -t ./hintparser/hintParser.atd
	atdgen -j ./hintparser/hintParser.atd

clean:
	rm ./hintparser/hintParser_j.mli
	rm ./hintparser/hintParser_t.mli
	rm ./hintparser/hintParser_j.ml
	rm ./hintparser/hintParser_t.ml
	$(OCAMLBUILD) -clean
