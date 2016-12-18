H = @

OPT  = ../../matitac.opt -elpi-quiet -elpi-cache
BYTE = ../../matitac     -elpi-quiet -elpi-cache

MA = nat.ma
LOG = log.txt
RUNS = 11

csc:
	$(H)echo > $(LOG)
	$(H)for RUN in `seq 1 $(RUNS)`; do touch $(MA); $(OPT) -elpi CSC $(MA) >> $(LOG); done
	$(H)grep "ELPI whole type-checking time:" $(LOG) | sort

fg1:
	$(H)echo > $(LOG)
	$(H)for RUN in `seq 1 $(RUNS)`; do touch $(MA); $(OPT) -elpi FG1 $(MA) >> $(LOG); done
	$(H)grep "ELPI whole type-checking time:" $(LOG) | sort

fg0:
	$(H)echo > $(LOG)
	$(H)for RUN in `seq 1 $(RUNS)`; do touch $(MA); $(OPT) -elpi FG0 $(MA) >> $(LOG); done
	$(H)grep "ELPI whole type-checking time:" $(LOG) | sort

no:
	$(H)echo > $(LOG)
	$(H)for RUN in `seq 1 $(RUNS)`; do touch $(MA); $(BYTE) -elpi NO $(MA) >> $(LOG); done
	$(H)grep "Matita whole type-checking time:" $(LOG) | sort
