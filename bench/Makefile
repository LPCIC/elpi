# Examples of usage:
#   make
#   make RUNNERS=elpi
#   make only JOB=rev14
#   make ... N=3 # repeat tests 3 times and plot an average
#
SHELL=/bin/bash
export TOP=$(abspath ..)

JOBS=$(sort $(notdir $(wildcard jobs/*)))
RUNNERS=$(sort $(filter-out %ulimit,$(notdir $(wildcard runners/*) $(wildcard ../elpi.git.*))))
MAX=59
TIME=timeout $(MAX) /usr/bin/time --quiet --format='%x %E %U %Mk' -o

define ulimit
ulimit -s `cat runners/$(call name,$(1)).ulimit`
endef

define time-log
((grep 'TIME' $(1) || echo '? ?') | cut -d ' ' -f 2-;\
 cat $(2)|cut -d ' ' -f 2-) | tr '\n' ' ' | sed 's/ /,/g'
endef

OK="\e[32mOK\e[0m"
KO="\e[31mKO\e[0m"

define check
if [ -z "`cat $(3)`" ]; then printf $(KO),$(5),$(2),$(MAX).00,0:$(MAX).00,$(MAX).00,0k;\
elif [ "`cat $(3)|cut -d ' ' -f 1`" = 0 -a $(1) = ok ];\
  then printf $(OK),$(5),$(2),`$(call time-log,$(4),$(3))`;\
elif [ "`cat $(3)|cut -d ' ' -f 1`" = 1 -a $(1) = ko ];\
  then printf $(OK),$(5),$(2),`$(call time-log,$(4),$(3))`;\
else printf $(KO),$(5),$(2),`$(call time-log,$(4),$(3))`;\
fi;\
printf "\n"
endef

define run
TMP=`mktemp`; LOG=`mktemp`;\
(export VARIANT=$(subst elpi,,$(2));\
 export CRUFT="`head -c $$RANDOM /dev/urandom|base64 -w0`";\
 $(call ulimit,$(2));\
 $(TIME) $$TMP `runners/$(call name,$(2)) $(3)` >$$LOG 2>&1;\
 $(call check,$(1),$(3),$$TMP,$$LOG,$(2)));\
rm $$TMP $$LOG;
endef

define runk
  $(foreach x,$(shell seq 1 $(1)), $(call run,$(2),$(3),$(4)))
endef

define name
$(patsubst elpi%,elpi,$(1))
endef

only: prepare
	@($(foreach r,$(RUNNERS),\
	  $(foreach k,ok ko,\
	   $(foreach j,\
	      $(sort $(wildcard jobs/$(call name,$(r))/$(k)/*$(JOB)*)),\
	    $(call runk,$(N),$(k),$(r),$(j)))))) | tee data.csv
	$(MAKE) plot

plot:
	@./plot data.csv
	@gnuplot data.csv.plot
	@echo Results: `ls $$PWD/*svg`

prepare:
	@make -C ..

.PHONY: all prepare only plot
