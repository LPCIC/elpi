# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus/source

.PHONY: all lists debug lkf-kernel eprover col064 binary_res_fol_nosub paramodulation resolution_steps runner checkers_col064
all: lists debug lkf-kernel eprover col064 binary_res_fol_nosub paramodulation resolution_steps runner checkers_col064

lists: lists.lp
debug: debug.lp
lkf-kernel: lkf-kernel.lp
eprover: eprover.lp
col064: col064.lp
binary_res_fol_nosub: binary_res_fol_nosub.lp
paramodulation: paramodulation.lp
resolution_steps: resolution_steps.lp
runner: runner.lp
checkers_col064: checkers_col064.lp

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
