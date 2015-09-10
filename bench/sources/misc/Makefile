# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus

.PHONY: all lists lists2 assoc reverse funs maps
all: lists lists2 assoc reverse funs maps
lists: lists.lp
lists2: lists2.lp
assoc: assoc.lp
reverse: reverse.lp
funs: funs.lp
maps: maps.lp

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

