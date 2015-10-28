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
OC=ocamlopt
OCB=ocamlc
OCP=ocamlopt

all:
	$(MAKE) pa_notrace.cmo pa_trace.cmo
	$(MAKE) elpi

trace:
	$(MAKE) pa_notrace.cmo pa_trace.cmo
	$(MAKE) elpi.trace

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
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o *.tex *.aux *.log *.pdf elpi elpi.trace elpi.git.*

dist:
	git archive --format=tar --prefix=elpi-$(V)/ HEAD . \
		| gzip > ../elpi-$(V).tgz

# compilation of elpi

elpi: elpi.$(CMX) latex_exporter.$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o $@ \
		camlp5.$(CMXA) unix.$(CMXA) str.$(CMXA) \
		parser.$(CMX) ptmap.$(CMX) \
		trace.$(CMX) runtime.$(CMX) \
    latex_exporter.$(CMX) \
		custom.$(CMX) elpi.$(CMX)

elpi.trace: elpi.trace.$(CMX) latex_exporter.$(CMX) runtime.trace.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o $@ \
		camlp5.$(CMXA) unix.$(CMXA) str.$(CMXA) \
		parser.$(CMX) ptmap.$(CMX) \
		trace.$(CMX) latex_exporter.$(CMX) runtime.trace.$(CMX) \
		custom.trace.$(CMX) elpi.trace.$(CMX)

%.$(CMX): %.ml
	$(OC) $(OCAMLOPTIONS) -pp '$(PP) pa_notrace.cmo' -c $<
%.trace.$(CMX): %.ml
	$(OC) $(OCAMLOPTIONS) -pp '$(PP) pa_trace.cmo' -c $<
	mv $*.$(CMX) $*.trace.$(CMX)
	mv $*.o $*.trace.o
%.cmi: %.mli
	$(OC) $(OCAMLOPTIONS) -c $<

parser.$(CMX): parser.ml parser.cmi 
	$(OCP) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

pa_trace.cmo: pa_trace.ml trace.cmi
	$(OCB)  -pp '$(PP) $(TRACESYNTAX) -DTRACE' $(FLAGS) -o $@ -c $<

pa_notrace.cmo: pa_trace.ml trace.cmi
	$(OCB)  -pp '$(PP) $(TRACESYNTAX)' $(FLAGS) -o $@ -c $<

# dependencies
elpi.$(CMX): elpi.ml ptmap.$(CMX) trace.$(CMX) runtime.$(CMX) latex_exporter.$(CMX) custom.$(CMX) parser.$(CMX)
elpi.trace.$(CMX): elpi.ml ptmap.$(CMX) trace.$(CMX) runtime.trace.$(CMX) latex_exporter.$(CMX) custom.trace.$(CMX) parser.$(CMX)
runtime.$(CMX): runtime.ml runtime.cmi trace.$(CMX) parser.$(CMX) ptmap.$(CMX)
runtime.trace.$(CMX): runtime.ml runtime.cmi trace.$(CMX) parser.$(CMX) ptmap.$(CMX)
runtime.cmi: runtime.mli parser.cmi
ptmap.cmi: ptmap.mli
ptmap.$(CMX): ptmap.ml ptmap.cmi
parser.cmi: parser.mli
trace.$(CMX): trace.ml trace.cmi
trace.cmi: trace.mli
custom.cmi: custom.mli
custom.$(CMX): custom.ml custom.cmi runtime.cmi runtime.$(CMX)
custom.trace.$(CMX): custom.ml custom.cmi runtime.cmi runtime.trace.$(CMX)
latex_exporter.cmi: latex_exporter.mli parser.cmi
latex_exporter.$(CMX): latex_exporter.ml latex_exporter.cmi parser.$(CMX) 

