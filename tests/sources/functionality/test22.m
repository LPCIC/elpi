:- module test22.

:- interface.

:- import_module io.

:- pred main(io::di, io::uo) is det.

:- implementation.

:- import_module list.
:- import_module int.

:- pred f(int::out) is det.
:- pred r(pred int).

:- mode r(out(pred(out) is det)) is det.

:- pred aux(int::out) is det.

aux(3).

f(X) :- r(P), P(X).

r(aux). 

main(!IO) :-
  f(S),
  io.write_line(S,!IO).