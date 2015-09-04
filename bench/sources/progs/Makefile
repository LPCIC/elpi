# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus

.PHONY: all eval curry tr1 tr2
all: eval curry tr1 tr2

eval: eval_examples.lp
curry: curry_test.lp
tr1: tr1_test.lp
tr2: tr2_test.lp

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
