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
OC=ocamlfind ocamlopt
OD=ocamlfind ocamldep

all:
	$(MAKE) trace_ppx
	$(MAKE) elpi

trace:
	$(MAKE) trace_ppx
	-mv elpi elpi.notrace
	$(MAKE) clean
	TRACE=1 $(MAKE) elpi
	mv elpi elpi.trace
	$(MAKE) clean
	-mv elpi.notrace elpi

trace_ppx: trace_ppx.ml
	ocamlfind query ppx_tools
	ocamlfind query ppx_deriving
	test `ocamlc -version` = 4.02.3
	$(OC) -package compiler-libs.common,ppx_tools.metaquot -linkpkg $< -o $@

git/%:
	rm -rf "$$PWD/elpi-$*"
	mkdir "elpi-$*"
	git clone -l .. "elpi-$*"
	cd "elpi-$*" && git checkout "$*" && cd elpi && make
	cp "elpi-$*/elpi/elpi" "elpi.git.$*"
	rm -rf "$$PWD/elpi-$*"

runners:
	true $(foreach t,$(shell git branch --list 'runner*' | cut -c 3-),\
		&& $(MAKE) git/$(t) && \
		mv elpi.git.$(t) elpi.git.$(t:runner-%=%))

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o *.tex *.aux *.log *.pdf
	rm -f elpi.git.* .depends .depends.parser

dist:
	git archive --format=tar --prefix=elpi-$(V)/ HEAD . \
		| gzip > ../elpi-$(V).tgz

# compilation of elpi

elpi: elpi.$(CMX) elpi_prolog_exporter.$(CMX) elpi_latex_exporter.$(CMX) elpi_runtime.$(CMX) elpi_parser.$(CMX)
	$(OC) -package ppx_deriving.std -linkpkg \
		$(OCAMLOPTIONS) $(FLAGS) -o $@ \
		camlp5.$(CMXA) unix.$(CMXA) str.$(CMXA) \
		elpi_ast.$(CMX) elpi_parser.$(CMX) elpi_ptmap.$(CMX) \
		elpi_trace.$(CMX) elpi_runtime.$(CMX) \
		elpi_latex_exporter.$(CMX) \
		elpi_prolog_exporter.$(CMX) \
		elpi_custom.$(CMX) elpi.$(CMX)

%.$(CMX): %.ml trace_ppx
	$(OC) $(OCAMLOPTIONS) -package ppx_deriving.std -ppx './trace_ppx' -c $<
%.cmi: %.mli
	$(OC) $(OCAMLOPTIONS) -c $<

elpi_parser.$(CMX): elpi_parser.ml elpi_parser.cmi elpi_ast.$(CMX) elpi_ast.cmi
	$(OC) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

# dependencies
include .depends .depends.parser

.depends: $(filter-out elpi_parser.ml, $(wildcard *.ml *.mli))
	$(OD) $^ > $@
.depends.parser: elpi_parser.ml
	$(OD) -pp '$(PP) $(PARSE)' $< > $@
# only registers hooks, not detected by ocamldep
elpi.cmx : elpi_custom.cmx
