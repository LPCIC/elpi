
:- module test30.

:- interface.

:- import_module io.
:- pred main(io::di, io::uo) is det.
:- implementation.

:- import_module int.

:- pred r(int::out, int::out) is det.

r(5,5).
r(4,5).

:- pred p(pred int).
:- mode p(in(pred(out) is det)) is det.

p(X) :- X(_).

:- pred q(int::out) is det.

q(X) :- p(r(X)).

main(!_).
