H=@

include Makefile.defs

SUBDIRS = components matita

ifeq ($(DISTRIBUTED),yes)
# 'world' is the default target when distributed, otherwise 'all' is
world: depend $(foreach d,$(SUBDIRS),rec@world@$(d))
all: depend $(foreach d,$(SUBDIRS),rec@all@$(d))
opt: depend $(foreach d,$(SUBDIRS),rec@opt@$(d))
else
all: $(foreach d,$(SUBDIRS),rec@all@$(d))
opt: $(foreach d,$(SUBDIRS),rec@opt@$(d))
world: depend $(foreach d,$(SUBDIRS),rec@world@$(d))
endif
depend: depend-stamp
depend-stamp:
ifeq ($(HAVE_OCAMLOPT),yes)
 ifeq ($(DISTRIBUTED),yes)
	$(MAKE) $(foreach d,$(SUBDIRS),rec@depend.opt@$(d))
 else
	$(MAKE) $(foreach d,$(SUBDIRS),rec@depend@$(d))
 endif
else
	$(MAKE) $(foreach d,$(SUBDIRS),rec@depend@$(d))
endif
	$(H)touch depend-stamp

clean: 
	$(H)make $(foreach d,$(SUBDIRS),rec@clean@$(d)) || true
distclean: 
	$(H)make $(foreach d,$(SUBDIRS),rec@distclean@$(d)) || true
	$(H)rm -rf .matita library-stamp depend-stamp
install-indep: $(foreach d,$(SUBDIRS),rec@install-indep@$(d))
install-arch: $(foreach d,$(SUBDIRS),rec@install-arch@$(d))
install: install-indep install-arch
uninstall: $(foreach d,$(SUBDIRS),rec@uninstall@$(d))

rec@%:
	$(MAKE) -C $(word 2, $(subst @, ,$*)) $(word 1, $(subst @, ,$*)) DESTDIR=$(DESTDIR)

# {{{ Distribution stuff

ifeq ($(DISTRIBUTED),yes)
library: library-stamp
library-stamp:
	$(MAKE) -C matita/ dist_library
	touch $@
endif

BASENAME = matita
NULL =
DISTDIR = $(BASENAME)-$(MATITA_VERSION)
CLEAN_ON_DIST = 		\
	components/license	\
	matita/TPTP/		\
	matita/contribs/	\
	components/binaries/matitaprover/benchmarks/ \
	matita/library/		\
	matita/nlibrary/	\
	matita/scripts/	\
	matita/tests/	\
	matita/lib/lambdaN/	\
	matita/lib/lambda/	\
	$(NULL)
EXTRA_DIST = 			\
	matita/AUTHORS 		\
	matita/LICENSE 		\
	matita/dist/BUGS 	\
	matita/dist/ChangeLog	\
	matita/dist/COPYING 	\
	Makefile 		\
	Makefile.defs.in	\
	$(NULL)
EXTRA_DIST_matita =			\
	matita/matitaGeneratedGui.ml	\
	$(NULL)

distcheck: dist dist_extract dist_test

dist: dist_mktmpdir dist_pre dist_export dist_mktarball dist_rmtmpdir
dist/configure.ac: configure.ac matita/dist/configure.ac.sed
	sed -f matita/dist/configure.ac.sed < $< > $@
dist/configure: dist/configure.ac
	cd dist && autoconf
dist_mktmpdir:
	test -d dist || mkdir dist
dist_rmtmpdir:
	test -d dist && rm -rf dist/ || true
dist_pre:
	$(MAKE) -C matita dist_pre
dist_export: dist/configure
	rm -rf $(DISTDIR)
	mkdir $(DISTDIR)
	svn export components $(DISTDIR)/components
	svn export matita $(DISTDIR)/matita
	(cd $(DISTDIR) && find . -name .depend -exec rm \{\} \;)
	(cd $(DISTDIR) && find . -name .depend.opt -exec rm \{\} \;)
	(cd $(DISTDIR) && rm -rf $(CLEAN_ON_DIST))
	cp $< $(DISTDIR)/configure
	cp dist/configure.ac $(DISTDIR)/configure.ac 
	cp -r $(EXTRA_DIST) $(DISTDIR)
	cp -r $(EXTRA_DIST_matita) $(DISTDIR)/matita
	# distribute HTML version of the manual
	mkdir -p $(DISTDIR)/docs/manual/
	$(MAKE) -C matita/help/C/ install DESTDIR=$(CURDIR)/$(DISTDIR)/docs/manual/
dist_mktarball:
	tar czf $(DISTDIR).tar.gz $(DISTDIR)
	#tar cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)

dist_extract:
	tar xzf $(DISTDIR).tar.gz
dist_test:
	(cd $(DISTDIR)/ \
	  && ./configure \
	  && $(MAKE) world \
	  && $(MAKE) install DESTDIR=`pwd`/install)

.PHONY: dist dist_export dist_mktarball distcheck dist_extract dist_test dist_autotools

# }}} End of distribution stuff

.PHONY: all opt clean distclean

# vim: set foldmethod=marker:
