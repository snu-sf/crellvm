LLVM_OCAML_LIB = /home/yongho.yoon/upgrade_simpleberry/simplberry/.local/lib/ocaml
LLVM_LIB = ../../.local/lib
VELLVM_LIB = ../../lib/vellvm/src/Extraction
YOJSON_LIB = $(VALLVM_HOME)/src/validator/lib/yojson-1.1.5
BINIOU_LIB = $(VALLVM_HOME)/src/validator/lib/biniou-1.0.5
EASY_FORMAT_LIB = $(VALLVM_HOME)/src/validator/lib/easy-format-1.0.1

LIB_FILES = llvm.cmxa,llvm_analysis.cmxa,llvm_executionengine.cmxa,llvm_target.cmxa,llvm_bitreader.cmxa,llvm_bitwriter.cmxa,llvm_scalar_opts.cmxa

OCAMLBUILD = ocamlbuild
OCAMLBUILD_OPT = -r \
	-I extraction \
	-I vellvm/src/Extraction \
	-use-ocamlfind -pkg yojson \
	-cflags -I,$(LLVM_OCAML_LIB) \
	-cflags -g\
	-lflags -I,$(LLVM_OCAML_LIB) \
	-lflags -cc,g++\
	-lflags -cclib,-lLLVMlib_json\
	-lflags -cclib,-lLLVMWriter\
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
	coq2ml.ml parseHints.ml printHints.ml translateHints.ml\
	main.ml utility.ml propagateHints.ml addInferenceHints.ml microHints.ml tt.ml

main.native: $(MLS)
	$(OCAMLBUILD) $(OCAMLBUILD_OPT) main.native

clean:
	$(OCAMLBUILD) -clean
