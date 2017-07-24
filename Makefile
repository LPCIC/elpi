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
OD=ocamlfind ocamldep

ifeq "$(BYTE)" ""
CMX=cmx
CMXA=cmxa
EXE=elpi
OC=ocamlfind ocamlopt
DEPS=.depends .depends.parser
OCNAME=OCAMLOPT
else
CMX=cmo
CMXA=cma
EXE=elpi.byte
OC=ocamlfind ocamlc
DEPS=.depends.byte .depends.parser.byte
OCNAME=OCAMLC
endif

ifeq "$(findstring install,$(MAKECMDGOALS))$(findstring uninstall,$(MAKECMDGOALS))" ""
OCAMLPATH:=$(shell pwd)/findlib:$(OCAMLPATH)
export OCAMLPATH
endif
H=@
pp = printf '$(1) %-26s %s\n' "$(3)" "$(2)"

all: check-ocaml-ver $(EXE)

byte:
	$(H)$(MAKE) BYTE=1 all

trace_ppx: trace_ppx.ml
	$(H)$(call pp,OCAMLOPT,-o,$@)
	$(H)ocamlfind ocamlopt -package ppx_tools_versioned.metaquot_402 \
		-package ocaml-migrate-parsetree.driver-main \
		-open Ast_402 \
		-c $< 
	$(H)ocamlfind ocamlopt -package ppx_tools_versioned.metaquot_402 \
		-package ocaml-migrate-parsetree \
		-predicates custom_ppx,ppx_driver \
		-linkpkg -linkall \
		trace_ppx.cmx \
		`ocamlfind query -predicates native \
	       		ocaml-migrate-parsetree.driver-main -a-format` \
		-o $@
	$(H)cp .merlin.in .merlin
	$(H)echo "FLG -ppx '$(shell pwd)/trace_ppx --as-ppx'" >> .merlin

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
	$(H)rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o *.a *.tex *.aux *.log *.pdf *.cmt *.cmti
	$(H)rm -f elpi.git.* trace_ppx elpi elpi.byte
	$(H)rm -f .depends .depends.parser .depends.byte .depends.parser.byte
	$(H)rm -rf sanbox/ findlib/

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
  elpi_custom.$(CMX)

ELPI_LIBS = \
  elpi_quoted_syntax.elpi  elpi_typechecker.elpi  \
  pervasives.elpi pervasives-syntax.elpi

# Standard compilation
ELPI_EASY_COMPONENTS = \
  $(filter-out $(ELPI_PACKED_COMPONENTS), \
    $(filter-out $(ELPI_P5_COMPONENTS), $(ELPI_COMPONENTS)))


elpi.$(CMXA): $(ELPI_COMPONENTS)
	$(H)$(call pp,$(OCNAME),-a,$@)
	$(H)$(OC) $(OC_OPTIONS) -o $@ -a $(ELPI_COMPONENTS)

$(EXE): elpi_REPL.ml findlib/elpi/META
	$(H)rm -rf sandbox; mkdir sandbox; cp $< sandbox/
	$(H)$(call pp,$(OCNAME),-package elpi -o $@,$<)
	$(H)cd sandbox; $(OC) $(OC_OPTIONS) -package elpi \
		-o ../$@ $<
	$(H)rm -rf sandbox

elpi_runtime_trace_on.$(CMX) : elpi_runtime.ml elpi_runtime.cmi trace_ppx
	$(H)$(call pp,$(OCNAME),-c -ppx 'trace_ppx --on' -for-pack,$@)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std \
		-ppx './trace_ppx --as-ppx --on' \
		-for-pack Elpi_runtime_trace_on \
	       	-c $<
	$(H)$(OC) $(OCAMLOPTIONS) \
		-pack elpi_runtime.$(CMX) -o $@

elpi_runtime_trace_off.$(CMX) : elpi_runtime.ml elpi_runtime.cmi trace_ppx
	$(H)$(call pp,$(OCNAME),-c -ppx 'trace_ppx --off' -for-pack,$@)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std \
		-ppx './trace_ppx --as-ppx --off' \
		-for-pack Elpi_runtime_trace_off \
	       	-c $<
	$(H)$(OC) $(OCAMLOPTIONS) \
		-pack elpi_runtime.$(CMX) -o $@

$(ELPI_EASY_COMPONENTS) : %.$(CMX): %.ml
	$(H)$(call pp,$(OCNAME),-c,$@)
	$(H)$(OC) $(OCAMLOPTIONS) \
		-package camlp5,ppx_deriving.std \
	       	-c $<

elpi_API.cmi: elpi_API.mli
	$(H)$(call pp,$(OCNAME),-opaque -c,$@)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 -opaque -c $<
%.cmi: %.mli
	$(H)$(call pp,$(OCNAME),-c,$@)
	$(H)$(OC) $(OCAMLOPTIONS) -package camlp5 -c $<

elpi_parser.$(CMX): elpi_parser.ml elpi_parser.cmi elpi_ast.$(CMX) elpi_ast.cmi
	$(H)$(call pp,$(OCNAME),-c -pp camlp5o,$@)
	$(H)$(OC) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

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
# 
# META.%: LIBSPATH = $(shell pwd)
# META.%: meta.%.src
# 	$(H)cp $< $@
# 	$(H)(echo "directory=\"$(LIBSPATH)\"";\
# 	 echo "version=\"$(V)\"") >> $@
# 
findlib/elpi/META: elpi.$(CMXA) elpi.cmi Makefile
	$(H)rm -rf findlib/; mkdir findlib
	$(H)ocamlfind install -destdir $(shell pwd)/findlib -patch-archives \
		elpi META elpi_API.cmi elpi.cmi -optional elpi.cma elpi.cmxa elpi.a elpi_API.cmti

install:
	$(H)ocamlfind install -patch-archives \
		elpi META elpi_API.cmi $(ELPI_LIBS) \
		-optional elpi.cma elpi.cmxa elpi.a elpi_API.cmti elpi elpi.byte

uninstall:
	$(H)ocamlfind remove elpi

# required OCaml package
check-ocaml-ver:
	$(H)ocamlfind query camlp5 > /dev/null
	$(H)ocamlfind query ppx_tools_versioned > /dev/null
	$(H)ocamlfind query ppx_deriving > /dev/null
	$(H)ocamlfind query ocaml-migrate-parsetree.driver-main > /dev/null
