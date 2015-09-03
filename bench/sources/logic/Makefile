# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../source

.PHONY: all hcinterp hcsyntax pnf
all: hcinterp hcsyntax pnf
hcinterp: hcinterp_examples.lp
hcsyntax: hcsyntax_examples.lp
pnf: pnf_examples.lp

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
