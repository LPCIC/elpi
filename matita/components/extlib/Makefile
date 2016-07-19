PACKAGE = extlib
PREDICATES =

INTERFACE_FILES =		\
	componentsConf.mli 	\
        hExtlib.mli		\
	hMarshal.mli 		\
	patternMatcher.mli	\
	hLog.mli 		\
	trie.mli 		\
	discrimination_tree.mli 		\
	hTopoSort.mli 		\
	graphvizPp.mli		\
	$(NULL)
IMPLEMENTATION_FILES = \
	$(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN =

include ../../Makefile.defs
include ../Makefile.common
