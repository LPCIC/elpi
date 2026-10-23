help:
	@echo 'Build targets:'
	@echo
	@echo '  build                  builds elpi'
	@echo '  world                  builds elpi, ppx_elpi and elpi-lsp, all that install installs'
	@echo '  build-ppx              builds ppx_elpi (and its tests)'
	@echo '  build-lsp              builds elpi-lsp (needs sel, lsp)'
	@echo '  webrunner              builds Elpi on the web in webrunner/elpi-webrunner/: elpi-lsp and the API for JavaScript (needs lsp, js_of_ocaml, wasm_of_ocaml, node)'
	@echo '  install                installs all the packages (after make world)'
	@echo '  clean                  remove build artifacts'
	@echo '  release                release the software (note: git tag -s first)'
	@echo '  release-npm            publish the web build on npm (part of release)'
	@echo '  release-npm-preview    publish a preview of the web build on npm, with the dist-tag next'
	@echo '  pack-webrunner         the npm package of the web build, versioned by git describe'
	@echo
	@echo 'Testing targets:'
	@echo
	@echo '  tests                  runs the entire test suite'
	@echo '  tests ONLY=rex         runs only tests matching rex'
	@echo '  tests PROMOTE=true     runs and promote tests if different'
	@echo '                           (can be combined with ONLY)'
	@echo '  tests LN_NB=nb         sets max number of lines to print of failing tests'
	@echo '                           (negave numbers means print all file)'
	@echo '  tests STOP_ON_FST_ERROR=true stops the test suite after first error'
	@echo
	@echo '  tests-ppx              runs the ppx_elpi tests (alias runtest-ppx)'
	@echo '  tests-ppx PROMOTE=true runs and promotes the ppx_elpi tests if different'
	@echo '  tests-lsp              runs the elpi-lsp tests (alias runtest-lsp, needs sel, lsp)'
	@echo '  tests-lsp PROMOTE=true runs and promotes the elpi-lsp tests if different'
	@echo '  test-webrunner         runs the tests of the web build, also of its fallbacks (alias runtest-webrunner, needs node, npx)'
	@echo '  perf-lsp               times elpi-lsp on a big document: check vs requests (alias perf-lsp)'
	@echo
	@echo '  git/treeish            checkout treeish and build elpi.git.treeish'
	@echo
	@echo 'Documentation targets:'
	@echo
	@echo '  doc-build              build the user manual + API docs into docs/build/html'
	@echo '  doc-serve              build (if needed) and serve docs/build/html locally'
	@echo '  doc-serve DOC_PORT=n   ... on port n (default 8000)'
	@echo '  doc-publish            build and push the docs to the gh-pages branch'
	@echo
	@echo 'Parser maintenance targets:'
	@echo
	@echo '  menhir-repl            run menhir in interactive mode'
	@echo '  menhir-explain-conflicts'
	@echo '  menhir-complete-errormsgs run when updating the grammar'
	@echo '  menhir-strip-errormsgs remove comments from error message file'
	@echo
	@echo 'Options:'
	@echo
	@echo '  DUNE_OPTS="opts"       passes opts to dune (build, install and test targets)'
	@echo '                           e.g. make build DUNE_OPTS="--display short -j 4"'
	@echo

INSTALL=_build/install/default
BUILD=_build/default
SHELL:=/usr/bin/env bash
TIMEOUT=90.0
PROMOTE=false
LN_NB=-1
STOP_ON_FST_ERROR=false
PWD=$(shell pwd)
RUNNERS=\
  $(wildcard $(PWD)/_build/git/*/$(BUILD)/tests/sources/*.exe.git.*.exe) \
  $(wildcard $(PWD)/$(BUILD)/tests/sources/*.exe) \
  $(PWD)/$(INSTALL)/bin/elpi \
  $(PWD)/$(INSTALL)/bin/elpi-trace-elaborator \
  $(addprefix $(PWD)/,$(wildcard _build/git/*/$(INSTALL)/bin/elpi.git.*)) \
  $(shell if type tjsim >/dev/null 2>&1; then type -P tjsim; else echo; fi)
TIME=--time $(shell if type -P gtime >/dev/null 2>&1; then type -P gtime; else echo /usr/bin/time; fi)
STACK=1114112

DUNE_OPTS=

build:
	dune build $(DUNE_OPTS) @only-elpi

build-ppx:
	dune build $(DUNE_OPTS) @ppx_elpi/all

tests-ppx:
	dune build $(DUNE_OPTS) $(if $(filter true,$(PROMOTE)),--auto-promote) @runtest-ppx

# the server only (@@: not the targets of lsp/test, i.e. not the tests)
build-lsp:
	dune build $(DUNE_OPTS) @@lsp/default

tests-lsp:
	dune build $(DUNE_OPTS) $(if $(filter true,$(PROMOTE)),--auto-promote) @runtest-lsp

# Elpi on the web (webrunner/), in webrunner/elpi-webrunner/, the npm package:
# the entry points elpi-lsp-web.js (the server, in a web worker) and
# elpi-api.js (the API of Elpi for JavaScript), and what they load, compiled
# to JavaScript and to WebAssembly. It is always built in the release profile
# (the dev one gives a JavaScript file ten times bigger), and so are its
# tests, which test the very files that are packed
WEB_DIST=webrunner/elpi-webrunner
WEB_DUNE_OPTS=--profile=release $(DUNE_OPTS)
WEB_FILES=elpi-lsp-web.js web_lsp_driver.bc.js web_lsp_driver.bc.wasm.js \
  web_lsp_driver.bc.wasm.assets elpi-api.js elpi-api.d.ts web_api.bc.js
webrunner:
	dune build $(WEB_DUNE_OPTS) @webrunner/webrunner
	rm -rf $(WEB_DIST)
	mkdir -p $(WEB_DIST)
	cd _build/default/webrunner && cp -rf $(WEB_FILES) $(CURDIR)/$(WEB_DIST)/
	cp -f webrunner/npm/package.json webrunner/npm/README.md LICENSE $(WEB_DIST)/
	chmod -R u+w $(WEB_DIST)

# test-webrunner also typechecks webrunner/test/api/types.ts against
# webrunner/elpi-api.d.ts (with npx, which downloads TypeScript)
test-webrunner:
	dune build $(WEB_DUNE_OPTS) $(if $(filter true,$(PROMOTE)),--auto-promote) @runtest-webrunner
	npx --yes -p typescript@5.9.3 tsc --noEmit --strict --target es2020 --lib es2020,dom webrunner/test/api/types.ts

perf-lsp:
	dune build $(DUNE_OPTS) --force @lsp/perf/perf-lsp

# all the packages (elpi, ppx_elpi, elpi-lsp...): dune install needs them all
world:
	dune build $(DUNE_OPTS) @install

install:
	dune install $(DUNE_OPTS)

doc:
	dune build $(DUNE_OPTS) @doc

doc-build: doc
	dune build $(DUNE_OPTS) elpi_REPL.exe
	rm -rf docs/build
	rm -rf docs/source
	cp -r docs/base docs/source
	sed -i "s/@@VERSION@@/$(shell git describe)/" docs/source/conf.py
	python3 docs/engine/engine.py
	cd docs && make html
	# Graft the odoc API tree in, but keep Sphinx's index.html as the landing
	# page (odoc's own index.html is just a one-link package list).
	cp -r _build/default/_doc/_html/elpi _build/default/_doc/_html/odoc.support docs/build/html/
	touch docs/build/html/.nojekyll

DOC_PORT ?= 8000
doc-serve:
	@test -f docs/build/html/index.html || $(MAKE) doc-build
	@echo "Serving docs on http://localhost:$(DOC_PORT)/  (Ctrl-C to stop)"
	python3 -m http.server $(DOC_PORT) --directory docs/build/html

doc-publish: doc-build
	rm -rf /tmp/gh-pages
	cp -r docs/build/html/ /tmp/gh-pages
	OLD_BRANCH=`git branch --show-current`; \
	git checkout gh-pages && rm -rf * && cp -r /tmp/gh-pages/* ./ && rm -rf /tmp/gh-pages && git add . && git commit -m "Updated gh-pages" && git checkout $$OLD_BRANCH
	@echo "uploading: enter to continue, ^C to abort"; read DUMMY; git push origin gh-pages

clean:
	rm -rf _build
	rm -rf docs/build

release:
	dune-release -p elpi,ppx_elpi,elpi-lsp
	$(MAKE) release-npm

# the npm package of the web build (webrunner/elpi-webrunner/elpi-webrunner-VERSION.tgz,
# after make webrunner), with the version given by git
# describe: X.Y.Z on the tag vX.Y.Z, and X.Y.(Z+1)-dev.N.gHASH N commits after
# it, e.g. 3.9.3-dev.15.g6d9c3e5eef, which semver puts after 3.9.2 (and before
# 3.9.3): it can be installed with npm install
pack-webrunner:
	@d=$$(git describe --tags --long) || { echo 'pack-webrunner: git describe needs the tags' >&2; exit 1; }; \
	h=$${d##*-}; d=$${d%-*}; n=$${d##*-}; t=$${d%-*}; t=$${t#v}; \
	if [ "$$n" = 0 ]; then v=$$t; else v=$${t%.*}.$$(($${t##*.}+1))-dev.$$n.$$h; fi; \
	cd $(WEB_DIST) && \
	npm version --no-git-tag-version --allow-same-version "$$v" >/dev/null && \
	rm -f elpi-webrunner-*.tgz && npm pack

# the web build, published on npm as elpi-webrunner (webrunner/npm/), with the version
# of the tag of HEAD (vX.Y.Z); needs npm login, or a token in ~/.npmrc
release-npm:
	@tag=$$(git describe --tags --exact-match 2>/dev/null) || { echo 'release-npm: HEAD has no tag' >&2; exit 1; }; \
	$(MAKE) webrunner && \
	cd $(WEB_DIST) && \
	npm version --no-git-tag-version --allow-same-version "$${tag#v}" && \
	npm publish --access public

# a preview of the web build on npm: the package of pack-webrunner, versioned
# X.Y.(Z+1)-dev.N.gHASH, published with the dist-tag next instead of latest
# (npm install elpi-webrunner@next). HEAD must not be a tag (that is
# release-npm), and the tree must be clean (the version names HEAD). Needs npm
# login, or a token in ~/.npmrc; NPM_OPTS is passed to npm publish (e.g.
# NPM_OPTS=--otp=123456)
release-npm-preview:
	@if git describe --tags --exact-match >/dev/null 2>&1; then echo 'release-npm-preview: HEAD has a tag, see release-npm' >&2; exit 1; fi; \
	git diff --quiet HEAD || { echo 'release-npm-preview: the tree has uncommitted changes' >&2; exit 1; }; \
	$(MAKE) webrunner pack-webrunner && \
	cd $(WEB_DIST) && \
	npm publish elpi-webrunner-*.tgz --tag next --access public $(NPM_OPTS)

# testing
tests:
	dune build $(DUNE_OPTS) @only-elpi
	dune runtest
	ulimit -s $(STACK); OCAMLRUNPARAM=l=$(STACK) \
		dune exec tests/test.exe -- \
		--seed $$RANDOM \
		--promote $(PROMOTE) \
		--ln_nb=$(LN_NB) \
		--timeout $(TIMEOUT) \
		--stop-on-first-error=$(STOP_ON_FST_ERROR) \
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
	    (cd _build/install/default/bin/; ln -sf elpi elpi.git.$*); \
	    (cd _build/default/tests/sources; for x in *.exe; do ln -sf $$x $$x.git.$*.exe; done) \
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

.PHONY: release-npm release-npm-preview pack-webrunner tests tests-ppx build-ppx webrunner test-webrunner perf-lsp help install build world clean gh-pages doc doc-build doc-serve doc-publish
