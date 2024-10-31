:- module test1.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.
:- pred p(int::in, int::out) is nondet.

:- implementation.
:- import_module int.


p(1,2).
p(2,X) :- X = 3; X = 4.

main(!IO).