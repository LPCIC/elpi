PACKAGE = content_pres
PREDICATES =

INTERFACE_FILES =		 \
	renderingAttrs.mli	 \
	cicNotationLexer.mli	 \
	cicNotationParser.mli	 \
	mpresentation.mli	 \
	box.mli			 \
	content2presMatcher.mli	 \
	termContentPres.mli	 \
	boxPp.mli		 \
	cicNotationPres.mli	 \
	content2pres.mli	 \
	$(NULL)
IMPLEMENTATION_FILES =		 \
	$(INTERFACE_FILES:%.mli=%.ml)

cicNotationPres.cmi: OCAMLOPTIONS += -rectypes
cicNotationPres.cmo: OCAMLOPTIONS += -rectypes
cicNotationPres.cmx: OCAMLOPTIONS += -rectypes

all:
clean:

LOCAL_LINKOPTS = -package helm-content_pres -linkpkg

cicNotationLexer.cmo: OCAMLC = $(OCAMLC_P4)
cicNotationParser.cmo: OCAMLC = $(OCAMLC_P4)
cicNotationLexer.cmx: OCAMLOPT = $(OCAMLOPT_P4)
cicNotationParser.cmx: OCAMLOPT = $(OCAMLOPT_P4)
cicNotationLexer.ml.annot: OCAMLC = $(OCAMLC_P4)
cicNotationParser.ml.annot: OCAMLC = $(OCAMLC_P4)

include ../../Makefile.defs
include ../Makefile.common

# <cross> cross compatibility among ocaml 3.09 and ocaml 3.08, to be removed as
# soon as we have ocaml 3.09 everywhere and "loc" occurrences are replaced by
# "_loc" occurrences
UTF8DIR := $(shell $(OCAMLFIND) query helm-syntax_extensions)
ULEXDIR := $(shell $(OCAMLFIND) query ulex08)
MY_SYNTAXOPTIONS = -pp "camlp5o -I $(UTF8DIR) -I $(ULEXDIR) pa_extend.cmo pa_ulex.cma pa_unicode_macro.cma -loc loc"
cicNotationLexer.cmo: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
cicNotationParser.cmo: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
cicNotationLexer.cmx: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
cicNotationParser.cmx: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
cicNotationLexer.ml.annot: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
cicNotationParser.ml.annot: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
depend.opt: SYNTAXOPTIONS = $(MY_SYNTAXOPTIONS)
# </cross>

