help:
	@echo 'Build targets:'
	@echo
	@echo '  build            builds elpi'
	@echo '  install          install elpi'
	@echo '  clean            remove build artifacts'
	@echo
	@echo 'Testing targets:'
	@echo
	@echo '  tests            runs the entire test suite'
	@echo '  tests ONLY=rex   runs only tests matching rex'
	@echo
	@echo '  git/treeish      checkout treeish and build elpi.git.treeish'
	@echo
	@echo 'Parser maintenance targets:'
	@echo
	@echo '  menhir-repl      run menhir in interactive mode'
	@echo '  menhir-explain-conflicts'
	@echo '  menhir-complete-errormsgs run when updating the grammar'
	@echo '  menhir-strip-errormsgs remove comments from error message file'
	@echo

INSTALL=_build/install/default
BUILD=_build/default
SHELL:=/usr/bin/env bash
TIMEOUT=90.0
PWD=$(shell pwd)
RUNNERS=\
  dune \
  $(PWD)/$(INSTALL)/bin/elpi \
  $(addprefix $(PWD)/,$(wildcard _build/git/*/$(INSTALL)/bin/elpi.git.*)) \
  $(shell if type tjsim >/dev/null 2>&1; then type -P tjsim; else echo; fi)
TIME=--time $(shell if type -P gtime >/dev/null 2>&1; then type -P gtime; else echo /usr/bin/time; fi)
STACK=1114112
DUNE_OPTS=

CP5:=$(shell ocamlfind query camlp5)

build:
	dune build $(DUNE_OPTS) @all

install:
	dune install $(DUNE_OPTS)

doc:
	dune build $(DUNE_OPTS) @doc

clean:
	rm -rf _build

# testing
tests:
	$(MAKE) build
	dune runtest
	ulimit -s $(STACK); OCAMLRUNPARAM=l=$(STACK) \
		tests/test.exe \
		--seed $$RANDOM \
		--timeout $(TIMEOUT) \
		$(TIME) \
		--sources=$(PWD)/tests/sources/ \
		--plot=$(PWD)/tests/plot \
		$(addprefix --name-match ,$(ONLY)) \
		$(addprefix --cat-skip ,$(SKIP)) \
		$(addprefix --runner , $(RUNNERS))

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

# parser maintenance
menhir-repl:
	menhir --interpret src/parser/tokens.mly \
		src/parser/token_precedence.mly \
		--base grammar src/parser/grammar.mly 2>/dev/null
menhir-explain-conflicts:
	-menhir --explain src/parser/tokens.mly \
		src/parser/token_precedence.mly \
		--base grammar src/parser/grammar.mly
	echo "Plese look at grammar.conflicts"
menhir-complete-errormsgs:
	menhir src/parser/tokens.mly \
		src/parser/token_precedence.mly \
		--base grammar src/parser/grammar.mly \
		--list-errors > src/parser/error_messages.auto.messages
	menhir src/parser/tokens.mly \
		src/parser/token_precedence.mly \
		--base grammar src/parser/grammar.mly\
		--merge-errors src/parser/error_messages.auto.messages \
		--merge-errors src/parser/error_messages.txt \
		> src/parser/error_messages.merged
	mv src/parser/error_messages.merged src/parser/error_messages.txt
	rm src/parser/error_messages.auto.messages
menhir-strip-errormsgs:
	sed -e "/^##/d" -i.bak src/parser/error_messages.txt

.PHONY: tests help install build clean
