COQMODULE     := LLVMBerry
COQTHEORIES := extraction_defs.v extraction_validator.v $(wildcard ../exec/*.v)

all: extraction
	echo $(COQTHEORIES)

extraction: Makefile.coq
	$(MAKE) -f Makefile.coq extraction_defs.vo
	$(MAKE) -f Makefile.coq extraction_validator.vo

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-install none"; \
   echo "-R ../../coq $(COQMODULE)"; \
   echo "-R ../../lib/sflib sflib"; \
   echo "-R ../../lib/paco/src Paco"; \
   echo "-R ../../lib/vellvm/src Vellvm"; \
   echo "-R ../../lib/vellvm/lib/metalib metalib"; \
   echo "-R ../../lib/vellvm/lib/cpdtlib Cpdt"; \
   echo "-R ../../lib/vellvm/lib/compcert-2.4 compcert"; \
   echo $(COQTHEORIES)) > _CoqProject
	rm -f extraction_validator.vo
	rm -f extraction_defs.vo
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq
