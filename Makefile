TRACE=-DTRACE

PP=camlp5o -I . -I +camlp5
LIBS=unix.cmxa str.cmxa camlp5.cmxa $(EXTRALIB)
FLAGS=-g -I +camlp5
PPPARSE=-pp '$(PP) pa_extend.cmo pa_lexer.cmo'
PPTRACE=-pp '$(PP) pa_trace.cmo'
PPTRACESYNTAX=-pp '$(PP) pa_extend.cmo q_MLast.cmo pa_macro.cmo $(TRACE)'
EXTRALIB=cMap.cmx int.cmx bIA.cmx trace.cmx
LIBSBYTE=$(subst .cmx,.cmo,$(subst .cmxa,.cma,$(LIBS)))
H=@
I=@
ifneq "$(H)" "@"
I=@true
endif

all: elpi

elpi elpi.byte: test.ml lprun.cmx lpdata.cmx
	$(H) ocamlopt $(FLAGS) $(LIBS) lpdata.cmx lprun.cmx -o $@ $<
	$(H) ocamlc   $(FLAGS) $(LIBSBYTE) lpdata.cmo lprun.cmo -o $@.byte $<
	$(I) echo OCAMLC $<

lpdata.cmx lpdata.cmo: lpdata.ml $(EXTRALIB)
	$(H) ocamlopt $(PPPARSE) $(FLAGS) -o $@ -c $<
	$(H) ocamlc   $(PPPARSE) $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<
lprun.cmx lprun.cmo: lprun.ml $(EXTRALIB) lpdata.cmx pa_trace.cmo
	$(H) ocamlopt $(PPTRACE) $(FLAGS) -o $@ -c $<
	$(H) ocamlc   $(PPTRACE) $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<

pa_trace.cmo: pa_trace.ml trace.cmi
	$(H) ocamlc   $(PPTRACESYNTAX) $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<

%.cmx %.cmo: %.ml %.cmi
	$(H) ocamlopt $(FLAGS) -o $@ -c $<
	$(H) ocamlc   $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<
%.cmi: %.mli
	$(H) ocamlc   $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<

clean:
	$(H) rm -f *.cmo *.cmi *.cmx *.cma *.o elpi .depend

.depend: pa_trace.cmo
	$(H) ocamldep $(PPPARSE) -I +camlp5 lpdata.ml > $@
	$(H) ocamldep $(PPTRACESYNTAX) -I +camlp5  pa_trace.ml >> $@
	$(H) ocamldep $(PPTRACE) -I +camlp5 lprun.ml >> $@
	$(H) ocamldep -I +camlp5 \
		$(filter-out pa_trace.ml lpdata.ml lprun.ml,\
			$(wildcard *.ml *.mli)) >> $@
-include .depend


