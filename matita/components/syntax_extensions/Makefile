PACKAGE = utf8_macros
PREDICATES =
MAKE_TABLE_PACKAGES = helm-xml

# modules which have both a .ml and a .mli
INTERFACE_FILES = utf8Macro.mli 
IMPLEMENTATION_FILES = utf8MacroTable.ml $(INTERFACE_FILES:%.mli=%.ml)
EXTRA_OBJECTS_TO_INSTALL =
EXTRA_OBJECTS_TO_CLEAN =

all: utf8_macros.cma pa_unicode_macro.cma profiling_macros.cma

make_table: make_table.ml
	@echo "  OCAMLC $<"
	$(H)$(OCAMLFIND) ocamlc -rectypes -package $(MAKE_TABLE_PACKAGES) -linkpkg -o $@ $^

utf8MacroTable.ml:
	./make_table $@ $@.txt
utf8MacroTable.cmo: utf8MacroTable.ml
	@echo "  OCAMLC $<"
	$(H)@$(OCAMLFIND) ocamlc -c $<

pa_unicode_macro.cmo: pa_unicode_macro.ml utf8Macro.cmo
	@echo "  OCAMLC $<"
	$(H)@$(OCAMLFIND) ocamlc -rectypes -package camlp5 -pp "camlp5o q_MLast.cmo pa_extend.cmo -loc loc" -c $<
pa_unicode_macro.cma: utf8MacroTable.cmo utf8Macro.cmo pa_unicode_macro.cmo
	@echo "  OCAMLC -a $@"
	$(H)@$(OCAMLFIND) ocamlc -a -o $@ $^

profiling_macros.cmo: profiling_macros.ml
	@echo "  OCAMLC $<"
	$(H)@$(OCAMLFIND) ocamlc -package camlp5 -pp "camlp5o -loc loc" -c $<
profiling_macros.cma:profiling_macros.cmo
	@echo "  OCAMLC -a $@"
	$(H)@$(OCAMLFIND) ocamlc -a -o $@ $^
	

.PHONY: test
test: test.ml
	$(OCAMLFIND) ocamlc -package helm-utf8_macros -syntax camlp5o $< -o $@

clean:
distclean: extra_clean
extra_clean:
	rm -f make_table test

STATS_EXCLUDE = utf8MacroTable.ml

include ../../Makefile.defs
include ../Makefile.common

