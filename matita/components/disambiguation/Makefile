PACKAGE = disambiguation
INTERFACE_FILES =		\
	disambiguateTypes.mli	\
	disambiguate.mli \
	multiPassDisambiguator.mli
IMPLEMENTATION_FILES = \
	$(patsubst %.mli, %.ml, $(INTERFACE_FILES))

all:

clean:
distclean:

include ../../Makefile.defs
include ../Makefile.common

OCAMLARCHIVEOPTIONS += -linkall

disambiguateTypes.cmi: disambiguateTypes.mli
	@echo "  OCAMLC -rectypes $<"
	@$(OCAMLC) -c -rectypes $<
disambiguateTypes.cmo: disambiguateTypes.ml disambiguateTypes.cmi
	@echo "  OCAMLC -rectypes $<"
	@$(OCAMLC) -c -rectypes $<
disambiguateTypes.cmx: disambiguateTypes.ml disambiguateTypes.cmi
	@echo "  OCAMLOPT -rectypes $<"
	@$(OCAMLOPT) -c -rectypes $<

