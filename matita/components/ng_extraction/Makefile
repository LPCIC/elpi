PACKAGE = ng_extraction
PREDICATES =

INTERFACE_FILES = \
	nCicExtraction.mli \
 	coq.mli \
 	ocamlExtractionTable.mli  \
	mlutil.mli \
 	common.mli \
 	extraction.mli \
 	ocaml.mli \
	ocamlExtraction.mli
#	extract_env.mli \

IMPLEMENTATION_FILES = \
   miniml.ml $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = 
EXTRA_OBJECTS_TO_CLEAN =
%.cmo: OCAMLOPTIONS += -w Ae
%.cmi: OCAMLOPTIONS += -w Ae
%.cmx: OCAMLOPTIONS += -w Ae

include ../../Makefile.defs
include ../Makefile.common
