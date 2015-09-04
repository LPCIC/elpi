# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus

.PHONY: all hcinterp hcsyntax pnf logic
all: hcinterp hcsyntax pnf logic
run:
	$(TEYJUS)/tjsim -m 1 -b -s 'main.' logic
hcinterp: hcinterp_examples.lp
hcsyntax: hcsyntax_examples.lp
pnf: pnf_examples.lp
logic: logic.lp

# Everything after this point is generic and should be duplicated
# in user's makefiles

%.lpo : %.mod %.sig
	$(TEYJUS)/tjcc $*

%.lp : %.lpo
	$(TEYJUS)/tjlink $*

-include depend
depend: *.mod *.sig
	$(TEYJUS)/tjdepend *.mod > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp depend
