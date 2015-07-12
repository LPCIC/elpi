V=$(shell git describe --tags)
PP=camlp5o -I . -I +camlp5
PARSE=pa_extend.cmo pa_lexer.cmo
FLAGS=-I $(shell camlp5 -where)
OCAMLOPTIONS= -g
CMX=cmx
CMXA=cmxa
OC=ocamlopt
OCP=ocamlopt
MAIN=elpi

$(MAIN): $(MAIN).$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o $(MAIN) \
		camlp5.$(CMXA) unix.$(CMXA) \
		parser.$(CMX) ptmap.$(CMX) runtime.$(CMX) $(MAIN).$(CMX)

$(MAIN).$(CMX): $(MAIN).ml ptmap.$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c $(MAIN).ml

runtime.$(CMX) runtime.cmi: runtime.ml parser.$(CMX) ptmap.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c runtime.ml

ptmap.cmi: ptmap.mli
	$(OC) $(OCAMLOPTIONS) -c ptmap.mli

ptmap.$(CMX): ptmap.ml ptmap.cmi
	$(OC) $(OCAMLOPTIONS) -c ptmap.ml

parser.cmi: parser.mli
	$(OC) $(OCAMLOPTIONS) -c parser.mli

parser.$(CMX): parser.ml parser.cmi 
	$(OCP) $(OCAMLOPTIONS) -pp '$(PP) $(PARSE)' $(FLAGS) -o $@ -c $<

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o $(MAIN)

dist:
	git archive --format=tar --prefix=elpi-$(V)/ HEAD . \
		| gzip > ../elpi-$(V).tgz
