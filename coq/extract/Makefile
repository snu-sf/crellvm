COQMODULE     := LLVMBerry
COQTHEORIES := extract_defs.v extract_validator.v $(wildcard ../exec/*.v)

all: extract
	echo $(COQTHEORIES)

quick: extract-quick
	echo $(COQTHEORIES)

extract: Makefile.coq
	$(MAKE) -f Makefile.coq extract_defs.vo
	$(MAKE) -f Makefile.coq extract_validator.vo

extract-quick: Makefile.coq
	$(MAKE) -f Makefile.coq extract_defs.vio quick
	$(MAKE) -f Makefile.coq extract_validator.vio quick

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
	rm -f extract_validator.vo
	rm -f extract_defs.vo
	coq_makefile -f _CoqProject -o Makefile.coq

clean: Makefile.coq
	make -f Makefile.coq clean
	rm -f Makefile.coq
