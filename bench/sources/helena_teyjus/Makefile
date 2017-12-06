H   = @
TMP = tmp.txt

TJCC     = ../../../../teyjus/tjcc
TJLINK   = ../../../../teyjus/tjlink
TJSIM    = ../../../../teyjus/tjsim -b -k 271200
TJDEPEND = ../../../../teyjus/tjdepend
TIME     = `which time` -p -a -f "%U" -o $(TMP)
ADD      = ./add.opt -a 3

MODULES = $(shell cat Make)

all: grundlagen.lp
run: 
	$(TJSIM) -s main. grundlagen
depend: .depend

test: grundlagen.lp Makefile
	@echo SYM -s main. $(<:%.lp=%)
	$(H)$(TIME) $(TJSIM) -s main. $(<:%.lp=%)

profile: profile.txt Makefile

clean:
	$(H)$(RM) *.lp *.lpo .depend profile.txt *~

%.lpo: %.mod %.sig Makefile
	@echo CC $*
	$(H)$(TJCC) $*

%.lp: %.lpo Makefile
	@echo LINK $*
	$(H)$(TJLINK) $*

.depend: $(MODULES:%=%.mod) $(MODULES:%=%.sig) Makefile
	@echo DEPEND $(MODULES)
	$(H)$(TJDEPEND) $(MODULES) > $@

profile.txt: grundlagen3.lp Makefile
	@echo [31 times] SYM -s main. $(<:%.lp=%)
	$(H)for RUN in `seq 31`; do $(TIME) $(TJSIM) -s main. $(<:%.lp=%); done
	$(H)sort $(TMP) | uniq > $@
	$(H)$(RM) $(TMP)

add.opt: add.ml
	ocamlopt -o add.opt add.ml

pippo: LINE = $(TIME) $(TJCC) helena; $(TIME) $(TJCC) grundlagen3; $(TIME) $(TJLINK) grundlagen3

pippo: add.opt
	$(H)$(RM) $(TMP)
	$(H)$(H)for RUN in `seq 31`; do $(LINE); done;
	$(H)$(ADD) < $(TMP) | sort | uniq > profile.txt
	$(H)$(RM) $(TMP)

ifneq ($(MAKECMDGOALS), depend)
ifneq ($(MAKECMDGOALS), clean)
   include .depend   
endif
endif

.PHONY: all depend test profile clean
