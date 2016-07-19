H=@
export SHELL=/bin/bash

include ../Makefile.defs

# Warning: the modules must be in compilation order
NULL =
MODULES =			\
	extlib			\
	xml			\
	registry		\
	syntax_extensions	\
	thread			\
	logger			\
	ng_kernel		\
        ng_extraction           \
	getter			\
	library			\
	content		        \
	grafite			\
	ng_refiner              \
	ng_library 		\
	ng_cic_content		\
	disambiguation	        \
	ng_disambiguation	\
	ng_paramodulation	\
	content_pres		\
	grafite_parser          \
	ng_tactics		\
	grafite_engine          \
	$(NULL)

METAS = $(MODULES:%=METAS/META.helm-%)

ifeq ($(DISTRIBUTED),no)
	MODULES+=binaries
endif

all: metas $(MODULES:%=rec@all@%) 
opt: metas syntax-extensions $(MODULES:%=rec@opt@%)

ifeq ($(HAVE_OCAMLOPT),yes)
world: opt
else
world: all
endif
syntax-extensions:
	$(H)$(MAKE) -C syntax_extensions depend
	$(H)$(MAKE) -C syntax_extensions
depend: syntax-extensions $(MODULES:%=rec@depend@%)
depend.opt: syntax-extensions $(MODULES:%=rec@depend.opt@%)
install-arch: $(MODULES:%=rec@install@%)
install-indep:
uninstall: $(MODULES:%=rec@uninstall@%)
clean: $(MODULES:%=rec@clean@%) clean_metas

.stats: $(MODULES:%=rec@.stats@%)
	$(H)(for m in $(MODULES); do echo -n "$$m:"; cat $$m/.stats; done) \
	 | sort -t : -k 2 -n -r > .stats

rec@%:
	$(H)$(MAKE) -C $(word 2, $(subst @, ,$*)) $(word 1, $(subst @, ,$*))

EXTRA_DIST_CLEAN = \
	libraries-clusters.ps 	\
	libraries-clusters.pdf 	\
	libraries-ext.ps 	\
	libraries.ps 		\
	.dep.dot 		\
	.extdep.dot 		\
	.clustersdep.dot 	\
	$(NULL)

distclean: clean clean_metas
	$(H)rm -f $(METAS)
	$(H)rm -f configure config.log config.cache config.status
	$(H)rm -f $(EXTRA_DIST_CLEAN)

.PHONY: all opt world metas depend install uninstall clean clean_metas distclean

METAS/META.helm-%: METAS/meta.helm-%.src
	$(H)cp $< $@ && echo "directory=\"$(shell pwd)/$*\"" >> $@

SIMPLIFYDEPS = ../daemons/graphs/tools/simplify_deps/simplify_deps
$(SIMPLIFYDEPS):
	$(H)$(MAKE) -C $(dir $(SIMPLIFYDEPS))

.PHONY: .dep.dot
.dep.dot: $(SIMPLIFYDEPS)
	$(H)echo "digraph G {" > $@
	$(H)echo "   rankdir = TB ;" >> $@
	$(H)for i in $(MODULES); do \
		$(OCAMLFIND) query helm-$$i -recursive -p-format | \
		grep helm | \
		sed "s/^helm-/ \"$$i\" -> \"/g" | \
		sed "s/$$/\";/g" >> $@ ; \
	done
	$(H)mv $@ $@.old ; $(SIMPLIFYDEPS) < $@.old > $@ ; rm $@.old
	$(H)echo "}" >> $@

.PHONY: .alldep.dot
.alldep.dot:
	$(H)echo "digraph G {" > $@
	$(H)echo "   rankdir = TB ;" >> $@
	$(H)for i in $(MODULES); do \
		$(OCAMLFIND) query helm-$$i -recursive -p-format | \
			grep -v "pxp-" | \
			sed "s/^pxp/pxp[-*]/g" | \
			sed "s/^/ \"helm-$$i\" -> \"/g" | \
			sed "s/$$/\";/g" >> $@ ; \
	done
	$(H)mv $@ $@.old ; \
		./simplify_deps/simplify_deps.opt < $@.old > $@ ; \
		rm $@.old
	$(H)for i in $(MODULES); do \
		echo "\"helm-$$i\" [shape=box,style=filled,fillcolor=yellow];"\
			>> $@ ; \
	done
	$(H)echo "}" >> $@

.extdep.dot: .dep.dot
	$(H)STATS/patch_deps.sh $< $@
.clustersdep.dot: .dep.dot
	$(H)USE_CLUSTERS=yes STATS/patch_deps.sh $< $@

libraries.ps: .dep.dot
	$(H)dot -Tps -o $@ $<
libraries-ext.ps: .extdep.dot
	$(H)dot -Tps -o $@ $<
libraries-clusters.ps: .clustersdep.dot
	$(H)dot -Tps -o $@ $<
libraries-complete.ps: .alldep.dot
	$(H)dot -Tps -o $@ $<

ps: libraries.ps libraries-ext.ps libraries-clusters.ps

tags: TAGS
.PHONY: TAGS
TAGS:
	$(H)otags -vi -r .

metas: $(filter-out METAS/META.helm-binaries, $(METAS))
