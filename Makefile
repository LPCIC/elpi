# vars passed around by make
TRACE=-DTRACE
CC=ocamlc
CCP=ocamlc

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

profile/%:
	$(H) $(MAKE) $*  CCP="ocamlcp -P fmi" PROFILE=-p TRACE="$(TRACE)"
notrace/%:
	$(H) rm -f pa_trace.cmo
	$(H) $(MAKE) $*  CCP="$(CCP)" PROFILE="$(PROFILE)" TRACE=""

bench: notrace/elpi
	$(H) time -f '\ntime: %U (user) + %S (sys) = %E (wall)\nmem: %Mk\npagefaults: %F (major) + %R (minor)' ./elpi

valgrind: notrace/elpi
	$(H) valgrind --tool=cachegrind ./elpi
	
gprof: profile/notrace/elpi
	$(H) ./elpi
	$(H) gprof elpi > elpi.annot
	$(H) echo "profiling written to elpi.annot"

ocamlprof: profile/notrace/elpi.byte
	$(H) ./elpi.byte
	$(I) echo OCAMLPROF lpdata.ml lprun.ml int.ml cMap.ml
	$(H) ocamlprof $(TMP)/lpdata.ml > lpdata.annot.ml
	$(H) ocamlprof $(TMP)/lprun.ml > lprun.annot.ml
	$(H) ocamlprof int.ml > int.annot.ml
	$(H) ocamlprof cMap.ml > cMap.annot.ml

elpi: test.ml lprun.cmx lpdata.cmx $(EXTRALIB)
	$(I) echo OCAMLOPT $<
	$(H) $(CCO) $(FLAGS) $(LIBS) lpdata.cmx lprun.cmx -o $@ $<

elpi.byte: test.ml lprun.cmo lpdata.cmo $(EXTRALIB:%.cmx=%.cmo)
	$(I) echo OCAMLC $<
	$(H) $(CCP)  $(FLAGS) $(LIBSBYTE) lpdata.cmo lprun.cmo -o $@ $<

lpdata.cmx: lpdata.ml pa_trace.cmo
	$(I) echo OCAMLOPT $<
	$(H) $(CCO) -pp '$(PPPARSE)' $(FLAGS) -o lpdata.cmx -c $<

lpdata.cmo: lpdata.ml pa_trace.cmo
	$(I) echo OCAMLCP $<
	$(H) $(PPPARSE) pr_o.cmo $< -o $(TMP)/$<
	$(H) cp lpdata.cmi lpdata.mli $(TMP)
	$(H) $(CCP) $(FLAGS) -o lpdata.cmo -c $(TMP)/$<

lprun.cmx: lprun.ml pa_trace.cmo
	$(I) echo OCAMLOPT $<
	$(H) $(CCO) -pp '$(PPTRACE)' $(FLAGS) -o lprun.cmx -c $<

lprun.cmo: lprun.ml pa_trace.cmo
	$(I) echo OCAMLCP $<
	$(H) $(PPTRACE) pr_o.cmo $< -o $(TMP)/$<
	$(H) cp lprun.cmi lprun.mli $(TMP)
	$(H) $(CCP)  $(FLAGS) -o lprun.cmo -c $(TMP)/$<

pa_trace.cmo: pa_trace.ml trace.cmi
	$(I) echo OCAMLC $<
	$(H) $(CC)   -pp '$(PPTRACESYNTAX)' $(FLAGS) -o $@ -c $<

%.cmx %.cmo: %.ml %.cmi
	$(I) echo OCAMLOPT $<
	$(H) $(CCO) $(FLAGS) -c $<
	$(I) echo OCAMLCP $<
	$(H) $(CCP)  $(FLAGS) -c $<
%.cmi: %.mli
	$(I) echo OCAMLC $<
	$(H) $(CC)   $(FLAGS) -o $@ -c $<

clean:
	$(H) rm -rf *.cmo *.cmi *.cmx *.cma *.o elpi elpi.byte \
		*.annot.ml .depend elpi.annot gmon.out ocamlprof.dump $(TMP)

.depend: pa_trace.cmo
	$(H) mkdir -p $(TMP)
	$(H) ocamldep -native -pp '$(PPPARSE)' -I +camlp5 lpdata.ml > $@
	$(H) ocamldep -pp '$(PPTRACESYNTAX)' -I +camlp5  pa_trace.ml >> $@
	$(H) ocamldep -native -pp '$(PPTRACE)' -I +camlp5 lprun.ml >> $@
	$(H) ocamldep -native -I +camlp5 \
		$(filter-out pa_trace.ml lpdata.ml lprun.ml,\
			$(wildcard *.ml *.mli)) >> $@
-include .depend


