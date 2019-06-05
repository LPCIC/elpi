SHELL:=/bin/bash
TIMEOUT=60.0
RUNNERS=$(shell type -P ../elpi $(wildcard ../elpi.*)) $(shell if type tjsim >/dev/null 2>&1; then type -P tjsim; else echo; fi)
TIME=--time $(shell if type -P gtime >/dev/null 2>&1; then type -P gtime; else echo /usr/bin/time; fi)
BUILD=_build/default/
STACK=32768

help:
	@echo 'Known targets:'
	@echo
	@echo '  build          build the test utility'
	@echo '  man            manpage of the test utility'
	@echo
	@echo '  run            runs the entire test suite'
	@echo '  run ONLY=rex   runs only tests matching rex'
	@echo
	@echo '  clean          purges _build _log and plots'
	@echo
	@echo 'Known runners:'
	@echo
	@echo '  ' $(RUNNERS)


build: .merlin
	@dune build ./test.exe

man: build
	@$(BUILD)test.exe --help

run: build
	ulimit -s $(STACK); $(BUILD)test.exe \
		--seed $$RANDOM \
		--timeout $(TIMEOUT) \
		$(TIME) \
		$(addprefix --name-match ,$(ONLY)) \
		$(addprefix --runner , $(RUNNERS))

.merlin: dune
	@dune build .merlin

clean:
	rm -rf _log _build data.csv data.csv.dat data.csv.svg data.csv.plot 

