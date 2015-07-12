# Examples of usage:
#   make
#   make JOBS=newelpi-impl16
#   make RUNNERS=newelpi
#   make only JOB=newelpi-impl16/ok/rev14.elpi
SHELL=/bin/bash
export TOP=$(abspath ..)

JOBS=$(sort $(notdir $(wildcard jobs/*)))
RUNNERS=$(sort $(notdir $(wildcard runners/*)))
TIME=timeout 30 /usr/bin/time --quiet --format='%x %E %U %Mk' -o

define ulimit
ulimit -s `cat runners/$(1).ulimit`
endef

define time-log
((grep 'INTERNAL TIMING' $(1) || echo '? ? ?') | cut -d ' ' -f 3-;\
 cat $(2)|cut -d ' ' -f 2-) | tr '\n' ' ' | sed 's/ /,/g'
endef

OK="\e[32mOK\e[0m"
KO="\e[31mKO\e[0m"

define check
if [ -z "`cat $(3)`" ]; then printf $(KO),$(2),10.00,0:10.00,10.00,0k;\
elif [ "`cat $(3)|cut -d ' ' -f 1`" = 0 -a $(1) = ok ];\
  then printf $(OK),$(2),`$(call time-log,$(4),$(3))`;\
elif [ "`cat $(3)|cut -d ' ' -f 1`" = 1 -a $(1) = ko ];\
  then printf $(OK),$(2),`$(call time-log,$(4),$(3))`;\
else printf $(KO),$(2),`$(call time-log,$(4),$(3))`;\
fi;\
printf "\n"
endef

define run
TMP=`mktemp`; LOG=`mktemp`;\
($(call ulimit,$(2)); $(TIME) $$TMP `runners/$(2) $(3)` >$$LOG 2>&1;\
 $(call check,$(1),$(3),$$TMP,$$LOG));\
rm $$TMP $$LOG;
endef

define run-all
$(foreach ok,$(sort $(wildcard jobs/$(2)/ok/*)), $(call run,ok,$(1),$(ok))) 
$(foreach ko,$(sort $(wildcard jobs/$(2)/ko/*)), $(call run,ko,$(1),$(ko))) 
endef

all: prepare
	@$(foreach r,$(RUNNERS),\
	  $(foreach j,$(filter $(r)%,$(JOBS)),\
	   $(call run-all,$(r),$(j))))

PARSED_JOB=$(subst /, ,$(JOB))
only: prepare
	@$(foreach r,$(RUNNERS),\
	  $(foreach j,$(filter $(r)%,$(JOB)),\
	   $(call run,$(word 2,$(PARSED_JOB)),$(r),jobs/$(JOB))))

prepare:
	@make -C ..

.PHONY: all prepare only
