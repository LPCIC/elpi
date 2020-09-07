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
SHELL:=/usr/bin/env bash
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
	dune build $(DUNE_OPTS) @all ; RC=$$?; \
	( cp -r _build/default/src/.ppcache src/ 2>/dev/null || true ); \
	( echo "FLG -ppx './merlinppx.exe --as-ppx --cookie '\''elpi_trace=\"true\"'\'''" >> src/.merlin );\
	exit $$RC

install:
	dune install $(DUNE_OPTS)

doc:
	dune build $(DUNE_OPTS) @doc

clean:
	rm -rf _build

cleancache:
	$(foreach f, $(wildcard src/.ppcache/*), echo > $(f); )

tests:
	$(MAKE) build
	ulimit -s $(STACK); \
		tests/test.exe \
		--seed $$RANDOM \
		--timeout $(TIMEOUT) \
		$(TIME) \
		--sources=$(shell pwd)/tests/sources/ \
		--plot=$(shell pwd)/tests/plot \
		$(addprefix --name-match ,$(ONLY)) \
		$(addprefix --runner , $(RUNNERS))

test-noppx:
	dune build --workspace dune-workspace.noppx

git/%:
	rm -rf "_build/git/elpi-$*"
	mkdir -p "_build/git/elpi-$*"
	git clone -l . "_build/git/elpi-$*"
	cd "_build/git/elpi-$*" && git checkout "$*"
	cd "_build/git/elpi-$*" && \
	  if [ -f dune ]; then \
	    make build DUNE_OPTS="$(DUNE_OPTS) --root .";\
	    cd _build/install/default/bin/; \
		ln -sf elpi elpi.git.$*; \
	  else \
	    make; \
		mkdir -p _build/install/default/bin/; \
		ln -s $$PWD/elpi _build/install/default/bin/elpi.git.$*; \
	  fi

.PHONY: tests help .merlin install build clean
