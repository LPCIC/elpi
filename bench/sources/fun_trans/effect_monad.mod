module effect_monad.

unit_value_effM T (value_effM T).
unit_mnont_effM T (mnont_effM T value_effM).
unit_comp_effM T (comp_effM T value_effM).

bind_effM (value_effM T) K Res :- K T Res.

bind_effM (mnont_effM T F1) K (mnont_effM T Res) :-
  pi lt\ sigma R\
    lifted_term lt T =>
      bind_effM (F1 lt) K R,
      ( % CASE: result of binding is a value
        value_effM (F2 lt) = R,
        Res = (t\ value_effM (F2 t))
      ; % CASE: result of binding maybe non-termination or computation
        C (F2 lt) (F3 lt) = R,
        Res = (t\ C (F2 t) (F3 t))
      ).

bind_effM (comp_effM T F1) K Res :-
  pi lt\ sigma R\
    lifted_term lt T =>
      bind_effM (F1 lt) K R,
      ( % CASE: R does not contain lifted term
        Res = R
      ; % CASE: R contains lifted term
        ( % CASE: result of binding is a value
          value_effM (F2 lt) = R,
          Res = comp_effM T (t\ value_effM (F2 t))
        ; % CASE: result of binding maybe non-termination or computation
          C (F2 lt) (F3 lt) = R,
          Res = comp_effM T (t\ C (F2 t) (F3 t))
        )
      ).
