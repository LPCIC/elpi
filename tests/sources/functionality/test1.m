:- module test1.

:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is det.

:- implementation.
:- import_module int.

% To compile it: mkdir -p .aux && mmc test1.m -o .aux/test
p(1,2).
p(2,X) :- X = 3; X = 4.

:- import_module list.
:- pred fold(pred(T, Acc, Acc), list(T), Acc, Acc).
:- mode fold(in(pred(in, in, out) is det), in, in, out) is det.

fold(_,[],A,A).
fold(F,[X|XS],A,B) :- F(X,A,A1),fold(F,XS,A1,B).

succ(X,Y) :- Y = X + 1.

:- pred p(int::in, int::out) is nondet.
:- pred succ(int::in,int::out) is det.
:- pred giverel(pred(int)).
:- mode giverel(out(pred(out) is nondet)) is multi.
giverel(p(1)).
giverel(p(1)).
giverel(succ(1)).



main(!IO).