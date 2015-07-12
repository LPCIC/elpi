# Commands:
#  make       -- to compile elpi
#  make git/V -- to compile elpi.git.V out of git's commit/branch/tag V
#                such binary is then picked up automatically by the bench
#                system as an elpi like runner
#  make runners -- foreach git tag runner-V, do something like make git/V 


V=$(shell git describe --tags)
PP=camlp5o -I . -I +camlp5
PARSE=pa_extend.cmo pa_lexer.cmo
FLAGS=-I $(shell camlp5 -where)
OCAMLOPTIONS= -g
CMX=cmx
CMXA=cmxa
OC=ocamlopt
OCP=ocamlopt

all: elpi

git/%:
	rm -rf "$$PWD/elpi-$*"
	mkdir "elpi-$*"
	git clone -l .. "elpi-$*"
	cd "elpi-$*"; git checkout -b "build-this" "$*"; cd elpi; make
	cp "elpi-$*/elpi/elpi" "elpi.git.$*"
	rm -rf "$$PWD/elpi-$*"

runners:
	$(foreach t,$(shell git tag | grep ^runner),\
		$(MAKE) git/$(t); mv elpi.git.$(t) elpi.git.$(t:runner-%=%))

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o elpi elpi.git.*

dist:
	git archive --format=tar --prefix=elpi-$(V)/ HEAD . \
		| gzip > ../elpi-$(V).tgz

# compilation of elpi

elpi: elpi.$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o elpi \
		camlp5.$(CMXA) unix.$(CMXA) \
		parser.$(CMX) ptmap.$(CMX) runtime.$(CMX) elpi.$(CMX)

elpi.$(CMX): elpi.ml ptmap.$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c elpi.ml

runtime.$(CMX): runtime.ml runtime.cmi parser.$(CMX) ptmap.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c runtime.ml

runtime.cmi: runtime.mli parser.cmi
	$(OC) $(OCAMLOPTIONS) -c runtime.mli

ptmap.cmi: ptmap.mli
	$(OC) $(OCAMLOPTIONS) -c ptmap.mli

ptmap.$(CMX): ptmap.ml ptmap.cmi
	$(OC) $(OCAMLOPTIONS) -c ptmap.ml

parser.cmi: parser.mli
	$(OC) $(OCAMLOPTIONS) -c parser.mli

parser.$(CMX): parser.ml parser.cmi 
	$(OCP) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

