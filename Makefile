# Commands:
#  make       -- to compile elpi
#  make git/V -- to compile elpi.git.V out of git's commit/branch/tag V
#                such binary is then picked up automatically by the bench
#                system as an elpi like runner
#  make runners -- foreach git tag runner-V, do something like make git/V 


V=$(shell git describe --tags)
PP=camlp5o -I . -I +camlp5
PARSE=pa_extend.cmo pa_lexer.cmo
TRACESYNTAX=pa_extend.cmo q_MLast.cmo pa_macro.cmo
FLAGS=-I $(shell camlp5 -where)
OCAMLOPTIONS= -g -bin-annot
CMX=cmx
CMXA=cmxa
OC=OCAMLPATH=$(shell pwd) ocamlfind ocamlopt
OD=OCAMLPATH=$(shell pwd) ocamlfind ocamldep -native
H=@
pp = printf '$(1) %-26s %s\n' "$(3)" "$(2)"

all: check-ocaml-ver elpi

trace_ppx: trace_ppx.ml
	$(H)$(call pp,OCAMLOPT,-o,$@)
	$(H)$(OC) -package ppx_tools.metaquot \
		-linkpkg $< -o $@
	$(H)cp .merlin.in .merlin
	$(H)echo 'FLG -ppx $(shell pwd)/trace_ppx' >> .merlin

git/%:
	$(H)rm -rf "$$PWD/elpi-$*"
	$(H)mkdir "elpi-$*"
	$(H)git clone -l .. "elpi-$*"
	$(H)cd "elpi-$*" && git checkout "$*" && cd elpi && make
	$(H)cp "elpi-$*/elpi/elpi" "elpi.git.$*"
	$(H)rm -rf "$$PWD/elpi-$*"

runners:
	$(H)true $(foreach t,$(shell git branch --list 'runner*' | cut -c 3-),\
		&& $(MAKE) git/$(t) && \
		mv elpi.git.$(t) elpi.git.$(t:runner-%=%))

clean:
	$(H)rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o *.tex *.aux *.log *.pdf
	$(H)rm -f elpi.git.* .depends .depends.parser META.*

dist:
	$(H)git archive --format=tar --prefix=elpi-$(V)/ HEAD . \
		| gzip > ../elpi-$(V).tgz

# compilation of elpi

OC_OPTIONS = -linkpkg $(OCAMLOPTIONS) $(FLAGS)

ELPI_DEPENDS = camlp5.$(CMXA) unix.$(CMXA) str.$(CMXA)

# Compilation with trace_ppx and -pack
ELPI_PACKED_COMPONENTS = \
  elpi_runtime_trace_on.$(CMX) elpi_runtime_trace_off.$(CMX)

# Compilation with camlp5 preprocessing
ELPI_P5_COMPONENTS = elpi_parser.$(CMX)

# All files linked in the .cma
ELPI_COMPONENTS = \
  elpi_trace.$(CMX) \
  elpi_util.$(CMX) elpi_ast.$(CMX) $(ELPI_P5_COMPONENTS) elpi_ptmap.$(CMX) \
  elpi_data.$(CMX) \
  $(ELPI_PACKED_COMPONENTS) elpi_compiler.$(CMX) elpi_API.$(CMX) \
  elpi_latex_exporter.$(CMX) elpi_prolog_exporter.$(CMX) elpi_custom.$(CMX)

# Standard compilation
ELPI_EASY_COMPONENTS = \
  $(filter-out $(ELPI_PACKED_COMPONENTS), \
    $(filter-out $(ELPI_P5_COMPONENTS), $(ELPI_COMPONENTS)))


elpi.$(CMXA): $(ELPI_COMPONENTS)
	$(H)$(call pp,OCAMLOPT,-a,$@)
	$(H)$(OC) $(OC_OPTIONS) -o $@ -a $(ELPI_COMPONENTS)

elpi: elpi.$(CMX) META.elpi elpi.$(CMXA)
	$(H)$(call pp,OCAMLOPT,-package elpi -o,$@)
	$(H)$(OC) $(OC_OPTIONS) -package elpi \
		-o $@ elpi.$(CMX)

elpi_runtime_trace_on.$(CMX) : elpi_runtime.ml elpi_runtime.cmi trace_ppx
	$(H)$(call pp,OCAMLOPT,-c -ppx 'trace_ppx -on' -for-pack,$@)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std -ppx './trace_ppx -on' \
		-for-pack Elpi_runtime_trace_on \
	       	-c $<
	$(H)$(OC) $(OCAMLOPTIONS) \
		-pack elpi_runtime.$(CMX) -o $@

elpi_runtime_trace_off.$(CMX) : elpi_runtime.ml elpi_runtime.cmi trace_ppx
	$(H)$(call pp,OCAMLOPT,-c -ppx 'trace_ppx -off' -for-pack,$@)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std -ppx './trace_ppx -off' \
		-for-pack Elpi_runtime_trace_off \
	       	-c $<
	$(H)$(OC) $(OCAMLOPTIONS) \
		-pack elpi_runtime.$(CMX) -o $@

$(ELPI_EASY_COMPONENTS) elpi.$(CMX) : %.$(CMX): %.ml
	$(H)$(call pp,OCAMLOPT,-c,$@)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std \
	       	-c $<
%.cmi: %.mli
	$(H)$(call pp,OCAMLOPT,-c,$@)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 -c $<

elpi_parser.$(CMX): elpi_parser.ml elpi_parser.cmi elpi_ast.$(CMX) elpi_ast.cmi
	$(H)$(call pp,OCAMLOPT,-c -pp camlp5o,$@)
	$(H)$(OC) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

# dependencies
include .depends .depends.parser

.depends: $(filter-out elpi_parser.ml, $(wildcard *.ml *.mli))
	$(H)$(call pp,OCAMLDEP,,$@)
	$(H)$(OD) $^ > $@
.depends.parser: elpi_parser.ml
	$(H)$(call pp,OCAMLDEP,,$@)
	$(H)$(OD) -pp '$(PP) $(PARSE)' $< > $@
# Not detected by ocamldep
elpi.$(CMX) : elpi_custom.$(CMX)
elpi_runtime_trace_on.$(CMX) : elpi_util.$(CMX) elpi_data.$(CMX) elpi_ptmap.$(CMX) elpi_parser.$(CMX) elpi_ast.$(CMX) elpi_trace.$(CMX) elpi_runtime.cmi
elpi_runtime_trace_off.$(CMX) : elpi_util.$(CMX) elpi_data.$(CMX) elpi_ptmap.$(CMX) elpi_parser.$(CMX) elpi_ast.$(CMX) elpi_trace.$(CMX) elpi_runtime.cmi
elpi_API.$(CMX): elpi_runtime_trace_on.$(CMX) elpi_runtime_trace_off.$(CMX)
elpi_compiler.$(CMX): elpi_runtime_trace_off.$(CMX)

META.%: LIBSPATH = $(shell pwd)
META.%: meta.%.src
	$(H)cp $< $@
	$(H)(echo "directory=\"$(LIBSPATH)\"";\
	 echo "version=\"$(V)\"") >> $@

# required OCaml package
check-ocaml-ver:
	$(H)ocamlfind query ppx_tools > /dev/null
	$(H)ocamlfind query ppx_deriving > /dev/null
	$(H)test `ocamlc -version` = 4.02.3
