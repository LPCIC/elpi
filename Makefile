# vars passed around by make: default values
TRACE=
CCP=ocamlc
FLAVOUR=plain
PROFILE=
OCAMLCFLAGS=-g

CC=ocamlc
CCO=ocamlopt $(PROFILE)
PP=camlp5o -I . -I +camlp5
LIBS=unix.cmxa str.cmxa camlp5.cmxa $(EXTRALIB)
FLAGS=$(OCAMLCFLAGS) -I +camlp5 -I $(FLAVOUR)
PPPARSE=$(PP) pa_extend.cmo pa_lexer.cmo $(FLAVOUR)/pa_trace.cmo
PPTRACE=$(PP) $(FLAVOUR)/pa_trace.cmo
PPTRACESYNTAX=$(PP) pa_extend.cmo q_MLast.cmo pa_macro.cmo $(TRACE)
EXTRALIB=$(addprefix $(FLAVOUR)/,cMap.cmx int.cmx trace.cmx)
LIBSBYTE=$(subst .cmx,.cmo,$(subst .cmxa,.cma,$(LIBS)))
MODULES= $(FLAVOUR)/lpdata $(FLAVOUR)/lprun $(FLAVOUR)/elpi

CMXMODULES=$(addsuffix .cmx,$(MODULES))
CMOMODULES=$(addsuffix .cmo,$(MODULES))
H=@
I=@
ifneq "$(H)" "@"
I=@true
endif
TMP=$(FLAVOUR)/.tmp/

RECARGS=OCAMLCFLAGS="$(OCAMLCFLAGS)" \
	CCP="$(CCP)" \
	PROFILE="$(PROFILE)" \
	TRACE="$(TRACE)" \
	FLAVOUR="$(FLAVOUR)"

devel: trace-all
	$(H) ln -sf trace/elpi .

all-flavours: trace-all plain-all

all: $(FLAVOUR)/elpi $(addprefix $(FLAVOUR)/elpi,.byte .cmxa .cma)

profile-% : CCP=ocamlcp -P fmi
profile-% : FLAVOUR=profile
profile-% : OCAMLCFLAGS=-g
profile-% : PROFILE=-p
profile-% : TRACE=
profile-% :
	$(I) echo MAKE profile
	$(H) $(MAKE) $* $(RECARGS) --no-print-directory

trace-% : CCP=ocamlc
trace-% : FLAVOUR=trace
trace-% : OCAMLCFLAGS=-g
trace-% : PROFILE=
trace-% : TRACE=-DTRACE
trace-% :
	$(I) echo MAKE trace
	$(H) $(MAKE) $* $(RECARGS) --no-print-directory

plain-% : CCP=ocamlc
plain-% : FLAVOUR=plain
plain-% : OCAMLCFLAGS=-g -w -26
plain-% : PROFILE=
plain-% : TRACE=
plain-% :
	$(I) echo MAKE plain
	$(H) $(MAKE) $* $(RECARGS) --no-print-directory


bench/%: all
	$(H) time -f '\ntime: %U (user) + %S (sys) = %E (wall)\nmem: %Mk\npagefaults: %F (major) + %R (minor)' ./$*

valgrind/%: all
	$(H) valgrind --tool=cachegrind ./$*
	
gprof: profile/all
	-$(H) echo 'test\ny\n' | ./elpi refiner.elpi
	$(H) gprof ./elpi > elpi.annot
	$(H) echo "profiling written to elpi.annot"

ocamlprof: profile-all
	$(H) echo 'test\ny\n' | profile/elpi.byte refiner.elpi
	$(I) echo OCAMLPROF lpdata.ml lprun.ml int.ml cMap.ml
	$(H) ocamlprof $(TMP)/lpdata.ml > lpdata.annot.ml
	$(H) ocamlprof $(TMP)/lprun.ml > lprun.annot.ml
	$(H) ocamlprof int.ml > int.annot.ml
	$(H) ocamlprof cMap.ml > cMap.annot.ml

$(FLAVOUR)/elpi: $(FLAVOUR)/client.cmx $(CMXMODULES) $(EXTRALIB)
	$(I) echo $(FLAVOUR)/OCAMLOPT $@
	$(H) $(CCO) $(FLAGS) $(LIBS) $(CMXMODULES) -o $@ $<

$(FLAVOUR)/elpi.byte: $(FLAVOUR)/client.cmo $(CMOMODULES) $(EXTRALIB:%.cmx=%.cmo)
	$(I) echo $(FLAVOUR)/OCAMLC $@
	$(H) $(CCP)  $(FLAGS) $(LIBSBYTE) $(CMOMODULES) -o $@ $<

$(FLAVOUR)/elpi.cmxa: $(CMXMODULES) $(EXTRALIB)
	$(I) echo $(FLAVOUR)/OCAMLOPT -a $@
	$(H) $(CCO) $(FLAGS) -a $(EXTRALIB) $(CMXMODULES) -o $@

$(FLAVOUR)/elpi.cma: $(CMOMODULES) $(EXTRALIB:%.cmx=%.cmo)
	$(I) echo $(FLAVOUR)/OCAMLC -a $@
	$(H) $(CCP)  $(FLAGS) -a $(EXTRALIB:%.cmx=%.cmo) $(CMOMODULES) -o $@

$(FLAVOUR)/test: $(FLAVOUR)/test.cmx $(CMXMODULES) $(EXTRALIB)
	$(I) echo $(FLAVOUR)/OCAMLOPT $<
	$(H) $(CCO) $(FLAGS) $(LIBS) $(CMXMODULES) -o $@ $<

$(FLAVOUR)/test.byte: $(FLAVOUR)/test.cmo $(CMOMODULES) $(EXTRALIB:%.cmx=%.cmo)
	$(I) echo $(FLAVOUR)/OCAMLC $<
	$(H) $(CCP)  $(FLAGS) $(LIBSBYTE) $(CMOMODULES) -o $@ $<

$(FLAVOUR)/lpdata.cmx: lpdata.ml $(FLAVOUR)/pa_trace.cmo
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLOPT $<
	$(H) $(CCO) -pp '$(PPPARSE)' $(FLAGS) -o $@ -c $<

$(FLAVOUR)/lpdata.cmo: lpdata.ml $(FLAVOUR)/pa_trace.cmo
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLCP $<
	$(H) $(PPPARSE) pr_o.cmo $< -o $(TMP)/$<
	$(H) cp $(FLAVOUR)/lpdata.cmi lpdata.mli $(TMP)
	$(H) $(CCP) $(FLAGS) -o $@ -c $(TMP)/$<

$(FLAVOUR)/lprun.cmx: lprun.ml $(FLAVOUR)/pa_trace.cmo
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLOPT $<
	$(H) $(CCO) -pp '$(PPTRACE)' $(FLAGS) -o $@ -c $<

$(FLAVOUR)/lprun.cmo: lprun.ml $(FLAVOUR)/pa_trace.cmo
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLCP $<
	$(H) $(PPTRACE) pr_o.cmo $< -o $(TMP)/$<
	$(H) cp $(FLAVOUR)/lprun.cmi lprun.mli $(TMP)
	$(H) $(CCP)  $(FLAGS) -o $@ -c $(TMP)/$<

$(FLAVOUR)/pa_trace.cmo: pa_trace.ml $(FLAVOUR)/trace.cmi
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLC $<
	$(H) $(CC)   -pp '$(PPTRACESYNTAX)' $(FLAGS) -o $@ -c $<

$(FLAVOUR)/%.cmx $(FLAVOUR)/%.cmo: %.ml
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLOPT $<
	$(H) $(CCO) $(FLAGS) -o $@ -c $<
	$(I) echo $(FLAVOUR)/OCAMLCP $<
	$(H) $(CCP)  $(FLAGS) -o $@ -c $<
$(FLAVOUR)/%.cmi: %.mli
	$(H) mkdir -p $(FLAVOUR)/
	$(I) echo $(FLAVOUR)/OCAMLC $<
	$(H) $(CC)   $(FLAGS) -o $@ -c $<

clean:
	$(H) rm -rf plain/ trace/ profile/ \
		*.annot.ml depend elpi.annot gmon.out ocamlprof.dump

FLAVOURIZE=\
	 sed -E -e 's? ([a-zA-Z_-]+)\.cm(x|o|i)? $(FLAVOUR)/\1\.cm\2?g' | \
	 sed -E -e 's?^([a-zA-Z_-]+)\.cm(x|o|i)?$(FLAVOUR)/\1\.cm\2?g'

$(FLAVOUR)/depend: $(FLAVOUR)/pa_trace.cmo
	$(I) echo $(FLAVOUR)/OCAMLDEP
	$(H) mkdir -p $(TMP)
	$(H) > $@
	$(H) ocamldep -pp '$(PPTRACESYNTAX)' -I +camlp5  pa_trace.ml | \
		$(FLAVOURIZE) >> $@
	$(H) ocamldep -native -pp '$(PPPARSE)' -I +camlp5 lpdata.ml | \
		$(FLAVOURIZE) >> $@
	$(H) ocamldep -native -pp '$(PPTRACE)' -I +camlp5 lprun.ml  | \
		$(FLAVOURIZE) >> $@
	$(H) ocamldep -native $(filter-out -g,$(FLAGS)) \
		$(filter-out pa_trace.ml lpdata.ml lprun.ml,\
			$(wildcard *.ml *.mli)) | \
		$(FLAVOURIZE) >> $@
include $(FLAVOUR)/depend


