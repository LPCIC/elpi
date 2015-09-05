SOURCES = \
  utils \
  types terms typing oper_sem \
  poly_types poly_terms poly_typing poly_oper_sem \
  effect_monad \
  let_ext \
  part_eval \
  tp_terms \
  tp_let_ext \
  tp_part_eval \
  termination \
  trafo \
  cse \
  main

MAIN   = main
QUERY  = main \\\\\"\$$1\\\\\".
RESULT = main

all:	$(RESULT)

terzo:
	mocaml -I /hame/markusm/mysys/lib/ocaml/contrib make_terzo.ml $(SOURCES)

clean_terzo:
	rm -f tz_*

clean:	clean_terzo

-include LPrologMakefile
