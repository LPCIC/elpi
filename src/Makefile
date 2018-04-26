# Overview of the build process:
# - trace_ppx defines [%spy] and [%trace] used _only_ in elpi_runtime.ml
# - elpi_runtime.ml is compiled twice
#   - with -for-pack Elpi_runtime_trace_off and passing --off to trace_ppx,
#     then it is immediately packed to elpi_runtime_trace_off.cm[x]o
#   - with -for-pack Elpi_runtime_trace_on  and passing --on  to trace_ppx,
#     then it is immediately packed to elpi_runtime_trace_on.cm[x]o
#   - both runtimes are linked, and elpi_API.ml switches between the two
#     using first class modules
# - elpi_parser.ml uses camlp5 syntax extensions for describing extensible
#   grammars and lexers

BASE=$(shell pwd)/..
include ../Makefile.common

# Compilation with trace_ppx and -pack
ELPI_PACKED_COMPONENTS = \
  elpi_runtime_trace_on.$(CMX) elpi_runtime_trace_off.$(CMX)

# Compilation with camlp5 preprocessing
ELPI_P5_COMPONENTS = elpi_parser.$(CMX)

# All files linked in the .cma
ELPI_COMPONENTS = \
  elpi_util.$(CMX) \
  elpi_trace.$(CMX) \
  elpi_ast.$(CMX) $(ELPI_P5_COMPONENTS) elpi_ptmap.$(CMX) \
  elpi_data.$(CMX) \
  $(ELPI_PACKED_COMPONENTS) elpi_compiler.$(CMX) \
  elpi_API.$(CMX) elpi_builtin.$(CMX)

# Standard compilation
ELPI_EASY_COMPONENTS = \
  $(filter-out $(ELPI_PACKED_COMPONENTS), \
    $(filter-out $(ELPI_P5_COMPONENTS), $(ELPI_COMPONENTS)))

elpi.$(CMXA): $(ELPI_COMPONENTS)
	$(H)$(call pp,$(OCNAME),-a -o $@,*.$(CMX))
	$(H)$(OC) $(OC_OPTIONS) -o $@ -a $(ELPI_COMPONENTS)

elpi_runtime_trace_on.$(CMX) elpi_runtime_trace_off.$(CMX) : elpi_runtime.ml elpi_runtime.cmi ../trace_ppx
	$(H)$(call pp,$(OCNAME),-c -ppx 'trace_ppx --on' -for-pack,$<)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std \
		-ppx '../trace_ppx --as-ppx --on' \
		-for-pack Elpi_runtime_trace_on \
	       	-c $<
	$(H)$(OC) $(OCAMLOPTIONS) \
		-pack elpi_runtime.$(CMX) -o elpi_runtime_trace_on.$(CMX)
	$(H)rm elpi_runtime.$(CMX)
	$(H)$(call pp,$(OCNAME),-c -ppx 'trace_ppx --off' -for-pack,$<)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std \
		-ppx '../trace_ppx --as-ppx --off' \
		-for-pack Elpi_runtime_trace_off \
	       	-c $<
	$(H)$(OC) $(OCAMLOPTIONS) \
		-pack elpi_runtime.$(CMX) -o elpi_runtime_trace_off.$(CMX)
	$(H)rm elpi_runtime.$(CMX)

$(ELPI_EASY_COMPONENTS) : %.$(CMX): %.ml
	$(H)$(call pp,$(OCNAME),-c,$<)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std,re.str \
	       	-c $<

elpi_API.cmi: elpi_API.mli
	$(H)$(call pp,$(OCNAME),$(OOPAQUE) -c,$<)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 $(OOPAQUE) -c $<
elpi_builtin.cmi: elpi_builtin.mli
	$(H)$(call pp,$(OCNAME),$(OOPAQUE) -c,$<)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 $(OOPAQUE) -c $<
%.cmi: %.mli
	$(H)$(call pp,$(OCNAME),-c,$<)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 -c $<

elpi_parser.$(CMX): elpi_parser.ml elpi_parser.cmi elpi_ast.$(CMX) elpi_ast.cmi
	$(H)$(call pp,$(OCNAME),-c -pp camlp5o,$<)
	$(H)$(OC) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' -package re.str $(FLAGS) -w -27 -o $@ -c $<

# dependencies
include $(DEPS)

.depends: $(filter-out elpi_parser.ml, $(wildcard *.ml *.mli))
	$(H)$(call pp,OCAMLDEP,-native,$@)
	$(H)$(OD) -native $^ > $@
.depends.parser: elpi_parser.ml
	$(H)$(call pp,OCAMLDEP,-native,$@)
	$(H)$(OD) -native -pp '$(PP) $(PARSE)' $< > $@
.depends.byte: $(filter-out elpi_parser.ml, $(wildcard *.ml *.mli))
	$(H)$(call pp,OCAMLDEP,,$@)
	$(H)$(OD) $^ > $@
.depends.parser.byte: elpi_parser.ml
	$(H)$(call pp,OCAMLDEP,,$@)
	$(H)$(OD) -pp '$(PP) $(PARSE)' $< > $@
# Not detected by ocamldep
elpi_runtime_trace_on.$(CMX) : elpi_util.$(CMX) elpi_data.$(CMX) elpi_ptmap.$(CMX) elpi_parser.$(CMX) elpi_ast.$(CMX) elpi_trace.$(CMX) elpi_runtime.cmi
elpi_runtime_trace_off.$(CMX) : elpi_util.$(CMX) elpi_data.$(CMX) elpi_ptmap.$(CMX) elpi_parser.$(CMX) elpi_ast.$(CMX) elpi_trace.$(CMX) elpi_runtime.cmi
elpi_API.$(CMX): elpi_runtime_trace_on.$(CMX) elpi_runtime_trace_off.$(CMX)
elpi_compiler.$(CMX): elpi_runtime_trace_on.$(CMX) elpi_runtime_trace_off.$(CMX)

.NOTPARALLEL:
