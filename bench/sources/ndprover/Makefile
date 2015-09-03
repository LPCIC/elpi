# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus

.PHONY: inter
inter: inter.lp
run:
	tail -n +2 ../ndprover.stdin | \
		$(TEYJUS)/tjsim -m 1 \
		-s "`head -n 1 ../ndprover.stdin`" inter

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

