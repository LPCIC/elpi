PACKAGE = grafite_parser
PREDICATES =

INTERFACE_FILES = 		\
	grafiteParser.mli		\
	print_grammar.mli 	\
	$(NULL)
IMPLEMENTATION_FILES = $(INTERFACE_FILES:%.mli=%.ml)

all:
clean:

# <cross> cross compatibility among ocaml 3.09 and ocaml 3.08, to be removed as
# soon as we have ocaml 3.09 everywhere and "loc" occurrences are replaced by
# "_loc" occurrences
UTF8DIR = $(shell $(OCAMLFIND) query helm-syntax_extensions)
ULEXDIR = $(shell $(OCAMLFIND) query ulex08)
MY_SYNTAXOPTIONS = -pp "camlp5o -I $(UTF8DIR) -I $(ULEXDIR) pa_extend.cmo pa_ulex.cma pa_unicode_macro.cma -loc loc"
grafiteParser.cmo: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
grafiteParser.cmx: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend.opt: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
# </cross>
#
grafiteParser.cmo: OCAMLC = $(OCAMLC_P4)
grafiteParser.cmx: OCAMLOPT = $(OCAMLOPT_P4)

include ../../Makefile.defs
include ../Makefile.common
