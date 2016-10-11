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
OCAMLOPTIONS= -g
CMX=cmx
CMXA=cmxa
OC=OCAMLPATH=$(PWD) ocamlfind ocamlopt
OD=OCAMLPATH=$(PWD) ocamlfind ocamldep -native
H=@

all: check-ocaml-ver
	$(H)$(MAKE) --no-print-directory trace_ppx
	$(H)$(MAKE) --no-print-directory elpi.cmxa
	$(H)$(MAKE) --no-print-directory META.elpi
	$(H)$(MAKE) --no-print-directory elpi

trace: check-ocaml-ver
	$(H)$(MAKE) --no-print-directory trace_ppx
	-$(H)mv elpi elpi.notrace
	$(H)$(MAKE) --no-print-directory clean
	$(H)TRACE=1 $(MAKE) --no-print-directory elpi.cmxa
	$(H)$(MAKE) --no-print-directory elpi
	$(H)mv elpi elpi.trace
	$(H)$(MAKE) --no-print-directory clean
	-$(H)mv elpi.notrace elpi

trace_ppx: trace_ppx.ml
	$(H)$(OC) -package compiler-libs.common,ppx_tools.metaquot \
		-linkpkg $< -o $@

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

ELPI_COMPONENTS = \
  coqlib.$(CMX) univ.$(CMX) uGraph.$(CMX) \
  elpi_trace.$(CMX) \
  elpi_util.$(CMX) elpi_ast.$(CMX) elpi_parser.$(CMX) elpi_ptmap.$(CMX) \
  elpi_runtime.$(CMX) \
  elpi_latex_exporter.$(CMX) elpi_prolog_exporter.$(CMX)

elpi.cmxa: $(ELPI_COMPONENTS)
	@echo OCAMLOPT -a $@
	$(H)$(OC) $(OC_OPTIONS) -o $@ -a $(ELPI_COMPONENTS)

elpi: elpi.$(CMX) elpi_custom.$(CMX) META.elpi
	@echo OCAMLOPT $@
	$(H)$(OC) $(OC_OPTIONS) -package elpi \
		-o $@ elpi_custom.$(CMX) elpi.$(CMX)

%.$(CMX): %.ml trace_ppx
	@echo OCAMLOPT $@ $(if $(TRACE),TRACE=$(TRACE),)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5,ppx_deriving.std -ppx './trace_ppx'\
	       	-c $<
%.cmi: %.mli
	@echo OCAMLOPT $@
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 -c $<

elpi_parser.$(CMX): elpi_parser.ml elpi_parser.cmi elpi_ast.$(CMX) elpi_ast.cmi
	@echo OCAMLOPT $@
	$(H)$(OC) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

# dependencies
include .depends .depends.parser

.depends: $(filter-out elpi_parser.ml, $(wildcard *.ml *.mli))
	@echo OCAMLDEP $@
	$(H)$(OD) $^ > $@
.depends.parser: elpi_parser.ml
	@echo OCAMLDEP $@
	$(H)$(OD) -pp '$(PP) $(PARSE)' $< > $@
# only registers hooks, not detected by ocamldep
elpi.cmx : elpi_custom.cmx

META.%: LIBSPATH = $(PWD)
META.%: meta.%.src
	@cp $< $@
	@(echo "directory=\"$(LIBSPATH)\"";\
	 echo "version=\"$(V)\"") >> $@

# required OCaml package
check-ocaml-ver:
	$(H)ocamlfind query ppx_tools > /dev/null
	$(H)ocamlfind query ppx_deriving > /dev/null
	$(H)test `ocamlc -version` = 4.02.3
