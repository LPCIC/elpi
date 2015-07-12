/*
 * Predicates for transforming formulas into prenex normal form 
 * assuming classical logic equivalences. This is an example of 
 * analyzing formula structure, including recursion over bindings
 * and generating modified structure based on this analysis
 */

module  pnf.


quant_free perp.
quant_free tru.
quant_free A :- atom A.
quant_free (and B C) :- quant_free B, quant_free C.
quant_free (or B C) :- quant_free B, quant_free C.
quant_free (imp B C) :- quant_free B, quant_free C.

atom (path X Y) :- termp X, termp Y.
atom (adj X Y) :- termp X, termp Y.

termp a.
termp b.
termp c.
termp (f X) :- termp X.

(prenex B B) :- (quant_free B), !. 
(prenex (and B C) D) :- (prenex B U), (prenex C V), (merge (and U V) D).
(prenex (or B C) D) :- (prenex B U), (prenex C V), (merge (or U V) D).
(prenex (imp B C) D) :- (prenex B U), (prenex C V), (merge (imp U V) D).
(prenex (all B) (all D)) :- (pi X\ ((termp X) => (prenex (B X) (D X)))).
(prenex (some B) (some D)) :- (pi X\ ((termp X) => (prenex (B X) (D X)))).


/* This predicate is for moving out quantifiers appearing at the head of the 
immediate subformulas of a formula with a propositional connective as its 
top-level symbol */
(merge (and (all B) (all C)) (all D)) :-
       (pi X\ ((termp X) => (merge (and (B X) (C X)) (D X)))).
(merge (and (all B) C) (all D)) :- 
       (pi X\ ((termp X) => (merge (and (B X) C) (D X)))).
(merge (and B (all C)) (all D)) :- 
       (pi X\ ((termp X) => (merge (and B (C X)) (D X)))).

(merge (and (some B) C) (some D)) :- 
       (pi X\ ((termp X) => (merge (and (B X) C) (D X)))).
(merge (and B (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (and B (C X)) (D X)))).

(merge (or (all B) C) (all D)) :-
       (pi X\ ((termp X) => (merge (or (B X) C) (D X)))).
(merge (or B (all C)) (all D)) :-
       (pi X\ ((termp X) => (merge (or B (C X)) (D X)))).
(merge (or (some B) (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (or (B X) (C X)) (D X)))).
(merge (or (some B) C) (some D)) :-
       (pi X\ ((termp X) => (merge (or (B X) C) (D X)))).
(merge (or B (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (or B (C X)) (D X)))).

(merge (imp (all B) (some C)) (some D)) :- 
       (pi X\ ((termp X) => (merge (imp (B X) (C X)) (D X)))).
(merge (imp (all B) C) (some D)) :- 
       (pi X\ ((termp X) => (merge (imp (B X) C) (D X)))).
(merge (imp (some B) C) (all D)) :-
       (pi X\ ((termp X) => (merge (imp (B X) C) (D X)))).
(merge (imp B (all C)) (all D)) :-
       (pi X\ ((termp X) => (merge (imp B (C X)) (D X)))).
(merge (imp B (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (imp B (C X)) (D X)))).

(merge B B) :- (quant_free B).

formula one  (imp (all (X \ (path a X))) tru).
formula two  (imp (some (X \ (path a X))) tru).
formula three  (and (all (X \ (path a X))) (all (Y \ (path Y a)))).
formula four  (imp (some (X \ (path a X))) ((all (Y \ (path a Y))))).

(test N F) :- (formula N OF), (prenex OF F).

main :- (test one F1), (test two F2), (test three F3), (test four F4),!.

