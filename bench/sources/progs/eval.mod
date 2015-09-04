	
% An evaluator that builds in the interpretation of the defined constants 
% of the functional programming language

module  eval.

accumulate eval_basic.

eval  (cond X Y Z) V  :-  
                (eval X truth, eval Y V ; eval Z V), !.
eval  (fix F) V               :-  
                eval (F (fix F))  V, !.
eval  (&& X Y) V   :-  
                (eval X truth, eval Y truth, V = truth ;
                             V = false), !.
eval  (plus X Y) (c V) :-  
                eval X (c V1), eval Y (c V2), V is V1 + V2, !.
eval  (minus X Y) (c V)  :-  
                eval X (c V1), eval Y (c V2), V is V1 - V2, !.
eval  (times X Y) (c V)  :-  
                eval X (c V1), eval Y (c V2), V is V1 * V2, !.
eval  (lss X Y) V  :-  
                eval X (c V1), eval Y (c V2), (V1 < V2, V = truth ; 
                                               V = false), !. 
eval  (eq X Y) V  :- 
                eval X (c V1), eval Y (c V2), (V1 = V2, V = truth ;
                                                V = false), !.
eval (intp (c X)) truth :- !.
eval (intp Y) false.
eval (prp (pr X Y)) truth :- !.
eval (prp Y) false.
eval (fst (pr X Y)) V  :- eval X V.
eval (snd (pr X Y)) V  :- eval Y V.

eval (hd L) V :- eval L (cons V Tl).
eval (tl L) V :- eval L (cons Hd V).
eval (nullp L) V :- eval L V1, (V1 = null, V = truth;
                                V = false), !.

% These are the clauses for atomic (uninterpreted) values
eval truth truth.
eval false false.
eval (c Y) (c Y).
eval (pr X Y) (pr X Y).
eval (cons Hd Tl) (cons HdV TlV) :- eval Hd HdV, eval Tl TlV.
eval null null.


