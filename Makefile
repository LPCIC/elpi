#TRACE=-DTRACE
#PROFILE=-p
CC=ocamlc
CCO=ocamlopt $(PROFILE)

PP=camlp5o -I . -I +camlp5
LIBS=unix.cmxa str.cmxa camlp5.cmxa $(EXTRALIB)
FLAGS=-g -I +camlp5
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo pa_trace.cmo
PPTRACE=$(PP) pa_trace.cmo
PPTRACESYNTAX=$(PP) pa_extend.cmo q_MLast.cmo pa_macro.cmo $(TRACE)
EXTRALIB=cMap.cmx int.cmx trace.cmx
LIBSBYTE=$(subst .cmx,.cmo,$(subst .cmxa,.cma,$(LIBS)))
H=@
I=@
ifneq "$(H)" "@"
I=@true
endif
TMP=.tmp/

all: elpi elpi.byte

perf.byte: elpi.byte
	$(H) ./elpi.byte
	$(I) echo OCAMLPROF lpdata.ml lprun.ml int.ml cMap.ml
	$(H) ocamlprof $(TMP)/lpdata.ml > lpdata.annot.ml
	$(H) ocamlprof $(TMP)/lprun.ml > lprun.annot.ml
	$(H) ocamlprof int.ml > int.annot.ml
	$(H) ocamlprof cMap.ml > cMap.annot.ml

perf:
	$(H) make clean
	$(H) make PROFILE=-p elpi -j
	$(H) ./elpi
	$(H) gprof elpi > elpi.annot
	$(H) echo "profiling written to elpi.annot"

elpi: test.ml lprun.cmx lpdata.cmx $(EXTRALIB)
	$(H) $(CCO) $(FLAGS) $(LIBS) lpdata.cmx lprun.cmx -o $@ $<
	$(I) echo OCAMLOPT $<

elpi.byte: test.ml lprun.cmo lpdata.cmo $(EXTRALIB:%.cmx=%.cmo)
	$(H) $(CC)p  $(FLAGS) $(LIBSBYTE) lpdata.cmo lprun.cmo -o $@ $<
	$(I) echo OCAMLC $<

lpdata.cmx: lpdata.ml pa_trace.cmo
	$(H) $(CCO) -pp '$(PPPARSE)' $(FLAGS) -o lpdata.cmx -c $<
	$(I) echo OCAMLOPT $<

lpdata.cmo: lpdata.ml pa_trace.cmo
	$(H) $(PPPARSE) pr_o.cmo $< -o $(TMP)/$<
	$(H) cp lpdata.cmi lpdata.mli $(TMP)
	$(H) $(CC)p $(FLAGS) -o lpdata.cmo -c $(TMP)/$<
	$(I) echo OCAMLCP $<

lprun.cmx: lprun.ml pa_trace.cmo
	$(H) $(CCO) -pp '$(PPTRACE)' $(FLAGS) -o lprun.cmx -c $<
	$(I) echo OCAMLOPT $<

lprun.cmo: lprun.ml pa_trace.cmo
	$(H) $(PPTRACE) pr_o.cmo $< -o $(TMP)/$<
	$(H) cp lprun.cmi lprun.mli $(TMP)
	$(H) $(CC)p  $(FLAGS) -o lprun.cmo -c $(TMP)/$<
	$(I) echo OCAMLCP $<

pa_trace.cmo: pa_trace.ml trace.cmi
	$(H) $(CC)   -pp '$(PPTRACESYNTAX)' $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<

%.cmx %.cmo: %.ml %.cmi
	$(H) $(CCO) $(FLAGS) -c $<
	$(I) echo OCAMLOPT $<
	$(H) $(CC)p  $(FLAGS) -c $<
	$(I) echo OCAMLCP $<
%.cmi: %.mli
	$(H) $(CC)   $(FLAGS) -o $@ -c $<
	$(I) echo OCAMLC $<

clean:
	$(H) rm -rf *.cmo *.cmi *.cmx *.cma *.o elpi elpi.byte \
		*.annot.ml .depend $(TMP)

.depend: pa_trace.cmo
	$(H) mkdir -p $(TMP)
	$(H) ocamldep -native -pp '$(PPPARSE)' -I +camlp5 lpdata.ml > $@
	$(H) ocamldep -pp '$(PPTRACESYNTAX)' -I +camlp5  pa_trace.ml >> $@
	$(H) ocamldep -native -pp '$(PPTRACE)' -I +camlp5 lprun.ml >> $@
	$(H) ocamldep -native -I +camlp5 \
		$(filter-out pa_trace.ml lpdata.ml lprun.ml,\
			$(wildcard *.ml *.mli)) >> $@
-include .depend


