:- module test2.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module int.

:- pred p(int::in, int::out) is semidet.
p(1,2).
p(2,X) :- if true then (X = 3) else false.


main(!IO).