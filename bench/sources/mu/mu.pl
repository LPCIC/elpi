
ge(s(X),zero).


mu :- theorem(xcons(m,(xcons(u,(xcons(i,(xcons(i,(xcons(u,xnil))))))))), s(s(s(s(s(zero))))),Dummy), !.

theorem(xcons(m,(xcons(i,xnil))), Dummy, xcons(a,(xcons m (xcons i xnil)))).
theorem(R, Depth, xcons(xcons(N,R),P)) :-
    ge(Depth,zero),
    s(D)=Depth,
    theorem(S, D, P),
    rule(N, S, R).

rule(s(zero), S, R) :- rule1(S, R).
rule(s(s(zero)), S, R) :- rule2(S, R).
rule(s(s(s(zero))), S, R) :- rule3(S, R).
rule(s(s(s(s(zero)))), S ,R) :- rule4(S, R).

rule1(xcons(i,xnil), xcons(i,(xcons(u,xnil)))).
rule1(xcons(H,X),xcons(H,Y)) :-
    rule1(X,Y).

rule2(xcons(m,X),xcons(m,Y)) :- 
    append1(X,X,Y).

rule3(xcons(i,xcons(i,xcons(i,X))),xcons(u,X)).
rule3(xcons(H,X),xcons(H,Y)) :-
    rule3(X,Y).

rule4(xcons(u,xcons(u,X)),X).
rule4(xcons(H,X),xcons(H,Y)) :-
    rule4(X,Y).

append1(xnil,X,X).
append1(xcons(A,B),X,xcons(A,B1)) :-
    append1(B,X,B1).

once :- mu.

iter(zero,X).
iter(s(N),X) :- X, iter(N,X).

plus(zero,X,X).
plus(s(X),Y,s(S)) :- plus(X,Y,S).

mult(zero,X,zero).
mult(s(X),Y,Z) :- mult(X,Y,K), plus(Y,K,Z).

exp1(zero,X,s(zero)).
exp1(s(X),Y,Z) :- exp1(X,Y,K), mult(Y,K,Z).

main :-
 TEN = s(s(s(s(s(s(s(s(s(s(zero)))))))))),
 exp1(s(s(s(s(zero))))),TEN,TENTHOUSAND),
 iter(TENTHOUSAND,once).
