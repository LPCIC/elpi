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
  $(shell pwd)/$(INSTALL)/bin/elpi \
  $(addprefix $(shell pwd)/,$(wildcard elpi.git.*)) \
  $(shell if type tjsim >/dev/null 2>&1; then type -P tjsim; else echo; fi)
TIME=--time $(shell if type -P gtime >/dev/null 2>&1; then type -P gtime; else echo /usr/bin/time; fi)
STACK=32768
DUNE_OPTS=

# this is to work around https://github.com/ocaml/dune/issues/1212
.merlin:
	@dune build $(DUNE_OPTS) .merlin
	@for ppx in `ls $$PWD/_build/default/.ppx/*/ppx.exe`; do\
		if $$ppx --print-transformations | grep -q trace; then\
	      echo PKG ppx_deriving.std ppx_deriving.runtime >> .merlin;\
	      echo FLG -ppx \"$$ppx --as-ppx\" >> .merlin;\
	      echo PKG ppx_deriving.std ppx_deriving.runtime >> src/.merlin;\
	      echo FLG -ppx \"$$ppx --as-ppx\" >> src/.merlin;\
		fi;\
	done

build:
	@$(MAKE) --no-print-directory .merlin
	dune build $(DUNE_OPTS) @install; RC=$?; $(MAKE) --no-print-directory .merlin; exit $$RC

install:
	dune install $(DUNE_OPTS) 

doc:
	dune build $(DUNE_OPTS) @doc

clean:
	rm -rf _build

tests:
	dune build $(DUNE_OPTS) $(INSTALL)/bin/elpi
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
	rm -rf "$$PWD/elpi-$*"
	mkdir "elpi-$*"
	git clone -l . "elpi-$*"
	cd "elpi-$*" && git checkout "$*"
	cd "elpi-$*" && \
	  if [ -f dune ]; then dune build --root . $(DUNE_OPTS) @install; else make; fi
	cp "elpi-$*/elpi" "elpi.git.$*" || \
		cp "elpi-$*/$(INSTALL)/bin/elpi" "elpi.git.$*"
	rm -rf "$$PWD/elpi-$*"

.PHONY: tests help .merlin install build clean
