PP=camlp5o -I . -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo
FLAGS=-I $(shell camlp5 -where)
OCAMLOPTIONS= -g
CMX=cmx
CMXA=cmxa
OC=ocamlopt
OCP=ocamlopt
MAIN=elpi

$(MAIN): $(MAIN).$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) $(FLAGS) -o $(MAIN) camlp5.$(CMXA) unix.$(CMXA) parser.$(CMX) ptmap.$(CMX) runtime.$(CMX) $(MAIN).$(CMX)

$(MAIN).$(CMX): $(MAIN).ml ptmap.$(CMX) runtime.$(CMX) parser.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c $(MAIN).ml

runtime.$(CMX) runtime.cmi: runtime.ml parser.cmi parser.$(CMX) ptmap.cmi ptmap.$(CMX)
	$(OC) $(OCAMLOPTIONS) -c runtime.ml

ptmap.cmi: ptmap.mli
	$(OC) $(OCAMLOPTIONS) -c ptmap.mli

ptmap.$(CMX): ptmap.ml ptmap.cmi
	$(OC) $(OCAMLOPTIONS) -c ptmap.ml

parser.cmi: parser.mli
	$(OC) $(OCAMLOPTIONS) -c parser.mli

parser.$(CMX): parser.ml parser.cmi 
	$(OCP) $(OCAMLOPTIONS) -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<

clean:
	rm -f *.cmo *.cma *.cmx *.cmxa *.cmi *.o $(MAIN)

test: $(MAIN)
	@cd tests.elpi; ../$(MAIN) -test crypt.elpi
	@cd tests.elpi; ../$(MAIN) -test mu.elpi
	@cd tests.elpi; ../$(MAIN) -test queens.elpi
	@cd tests.elpi; ../$(MAIN) -test zebra.elpi
	@cd tests.elpi; ../$(MAIN) -test typeof.elpi
	@cd tests.elpi; ../$(MAIN) -test reduce_cbv.elpi
	@cd tests.elpi; ../$(MAIN) -test reduce_cbn.elpi
	@cd tests.elpi; ../$(MAIN) -test ski.elpi
	@cd tests.elpi; ../$(MAIN) -test grundlagen_reduced.elpi
	@cd tests.elpi; ../$(MAIN) -test grundlagen.elpi

dist:
	git archive --format=tar --prefix=elpi/ HEAD . | gzip > ../elpi.tgz

.PHONY: test clean
