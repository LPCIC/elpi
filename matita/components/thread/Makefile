
PACKAGE = thread
INTERFACE_FILES = threadSafe.mli extThread.mli
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)

all: thread_fake.cma
opt: thread_fake.cmxa

include ../../Makefile.defs
include ../Makefile.common

fake/threadSafe.cmi: fake/threadSafe.mli
	@echo "  OCAMLC $<"
	@cd fake/	\
		&& ocamlfind ocamlc -c threadSafe.mli
thread_fake.cma: fake/threadSafe.cmi
	@echo "  OCAMLC -a $@"
	@cd fake/	\
		&& ocamlfind ocamlc -a -o $@ threadSafe.ml	\
		&& cp $@ ../
thread_fake.cmxa: fake/threadSafe.cmi
	@echo "  OCAMLOPT -a $@"
	@cd fake/	\
		&& ocamlfind opt -a -o $@ threadSafe.ml	\
		&& cp $@ ../

clean: clean_fake
clean_fake:
	rm -f fake/*.cm[aiox] fake/*.cmxa fake/*.[ao]
	rm -f thread_fake.cma thread_fake.cmxa

