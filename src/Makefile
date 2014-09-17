all: coq_build driver

coq_build: coq
	+COQBIN=../../../installed/coq/bin/ make -C coq

driver: driver
	+VALLVM_HOME=`pwd`/../.. make -C driver
	ln -f -s ocaml/main.native main.native

clean: 
	+COQBIN=../../../installed/coq/bin/ make clean -C coq
	rm -f coq/*.ml coq/*.mli
	+VALLVM_HOME=`pwd`/../.. make clean -C ocaml
	rm -f main.native
