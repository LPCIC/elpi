DUNE := dune
DUNE_PREFIX := _build/default

tests_dir = tests
tests := $(notdir $(wildcard $(tests_dir)/*))

# All targets are phony targets since we want to rely on dune for
# dependency management.

.PHONY : all

all :
	dune build

ppx_show.opam : dune-project
	dune build ppx_show.opam

.PHONY : clean

clean :
	dune clean

.PHONY : install

install :
	dune build @install
	dune install

.PHONY : tests
tests : $(tests)

define foreach_test
.PHONY : $(test)
$(test) :
	$(DUNE) build $(tests_dir)/$(test)/$(test).exe
	$(DUNE_PREFIX)/$(tests_dir)/$(test)/$(test).exe
endef
$(foreach test,$(tests),$(eval $(foreach_test)))
