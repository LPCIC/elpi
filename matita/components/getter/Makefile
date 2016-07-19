
PACKAGE = getter

INTERFACE_FILES =		\
  	http_getter_wget.mli	\
	http_getter_logger.mli	\
	http_getter_misc.mli	\
	http_getter_const.mli	\
	http_getter_env.mli	\
	http_getter_storage.mli	\
	http_getter_common.mli	\
	http_getter.mli		\
	$(NULL)

IMPLEMENTATION_FILES = \
	http_getter_types.ml \
	$(INTERFACE_FILES:%.mli=%.ml)

include ../../Makefile.defs
include ../Makefile.common

