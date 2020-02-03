help:
	@echo 'Known targets:'
	@echo
	@echo '  build            builds elpi'
	@echo '  install          install elpi'
	@echo '  clean            remove build artifacts'
	@echo
	@echo '  .merlin          builds a .merlin file'
	@echo
	@echo '  tests            runs the entire test suite'
	@echo '  tests ONLY=rex   runs only tests matching rex'
	@echo
	@echo '  git/treeish      checkout treeish and build elpi.git.treeish'
	@echo

INSTALL=_build/install/default
BUILD=_build/default
SHELL:=/bin/bash
TIMEOUT=90.0
RUNNERS=\
  dune \
  $(shell pwd)/$(INSTALL)/bin/elpi \
  $(addprefix $(shell pwd)/,$(wildcard _build/git/*/$(INSTALL)/bin/elpi.git.*)) \
  $(shell if type tjsim >/dev/null 2>&1; then type -P tjsim; else echo; fi)
TIME=--time $(shell if type -P gtime >/dev/null 2>&1; then type -P gtime; else echo /usr/bin/time; fi)
STACK=32768
DUNE_OPTS=

build:
	dune build $(DUNE_OPTS) @install

install:
	dune install $(DUNE_OPTS)

doc:
	dune build $(DUNE_OPTS) @doc

clean:
	rm -rf _build

tests:
	dune build $(DUNE_OPTS) @install
	dune build $(DUNE_OPTS) $(BUILD)/tests/test.exe
	ulimit -s $(STACK); \
		$(BUILD)/tests/test.exe \
		--seed $$RANDOM \
		--timeout $(TIMEOUT) \
		$(TIME) \
		--sources=$(shell pwd)/tests/sources/ \
		--plot=$(shell pwd)/tests/plot \
		$(addprefix --name-match ,$(ONLY)) \
		$(addprefix --runner , $(RUNNERS))

git/%:
	rm -rf "_build/git/elpi-$*"
	mkdir -p "_build/git/elpi-$*"
	git clone -l . "_build/git/elpi-$*"
	cd "_build/git/elpi-$*" && git checkout "$*"
	cd "_build/git/elpi-$*" && \
	  if [ -f dune ]; then \
	    dune build --root . $(DUNE_OPTS) @install; \
	    cd _build/install/default/bin/; \
		ln -sf elpi elpi.git.$*; \
	  else \
	    make; \
		mkdir -p _build/install/default/bin/; \
		ln -s $$PWD/elpi _build/install/default/bin/elpi.git.$*; \
	  fi

.PHONY: tests help .merlin install build clean
