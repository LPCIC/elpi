# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus/source

.PHONY: all lists debug lkf-kernel eprover col060 binary_res_fol_nosub paramodulation resolution_steps runner checkers
all: lists debug lkf-kernel eprover col060 binary_res_fol_nosub paramodulation resolution_steps runner checkers

lists: lists.lp
debug: debug.lp
lkf-kernel: lkf-kernel.lp
eprover: eprover.lp
col060: col060.lp
binary_res_fol_nosub: binary_res_fol_nosub.lp
paramodulation: paramodulation.lp
resolution_steps: resolution_steps.lp
runner: runner.lp
checkers: checkers.lp

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
