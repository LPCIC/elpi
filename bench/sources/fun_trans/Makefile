# Modify the path to the Teyjus executables as needed
TEYJUS= ../../../../teyjus/source

.PHONY: all utils types terms typing oper_sem poly_types poly_terms poly_typing poly_oper_sem effect_monad let_ext part_eval tp_terms tp_let_ext tp_part_eval termination trafo cse terzo_stuff main fun_trans

all: utils types terms typing oper_sem poly_types poly_terms poly_typing poly_oper_sem effect_monad let_ext part_eval tp_terms tp_let_ext tp_part_eval termination trafo cse terzo_stuff main fun_trans

ifeq "$(RUNNER)" "elpi"
P=../../../elpi -test fun_trans.elpi
else
P=$(TEYJUS)/tjsim -m 1 -b -s 'main.' fun_trans 
endif

run:
	$(P)

utils: utils.lp
types: types.lp
terms: terms.lp
typing: typing.lp
oper_sem: oper_sem.lp
poly_types: poly_types.lp
poly_terms: poly_terms.lp
poly_typing: poly_typing.lp
poly_oper_sem: poly_oper_sem.lp
effect_monad: effect_monad.lp
let_ext: let_ext.lp
part_eval: part_eval.lp
tp_terms: tp_terms.lp
tp_let_ext: tp_let_ext.lp
tp_part_eval: tp_part_eval.lp
termination: termination.lp
trafo: trafo.lp
cse: cse.lp
main: main.lp
fun_trans: fun_trans.lp
terzo_stuff: terzo_stuff.lp


# Everything after this point is generic and should be duplicated
# in user's makefiles

%.lpo : %.mod %.sig
	$(TEYJUS)/tjcc $*

%.lp : %.lpo
	$(TEYJUS)/tjlink $*

-include depend
depend: *.mod *.sig
	$(TEYJUS)/tjdepend *.mod > depend-stage
	mv depend-stage depend

.PHONY: clean
clean:
	rm -f *.lpo *.lp depend
