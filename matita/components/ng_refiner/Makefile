PACKAGE = ng_refiner
PREDICATES =

INTERFACE_FILES = \
	nDiscriminationTree.mli \
	nCicMetaSubst.mli \
	nCicUnifHint.mli \
	nCicCoercion.mli \
  nCicRefineUtil.mli \
	nCicUnification.mli \
	nCicRefiner.mli

IMPLEMENTATION_FILES = \
  $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL = 
EXTRA_OBJECTS_TO_CLEAN =
%.cmo: OCAMLOPTIONS += -w Ae
%.cmi: OCAMLOPTIONS += -w Ae
%.cmx: OCAMLOPTIONS += -w Ae

include ../../Makefile.defs
include ../Makefile.common

