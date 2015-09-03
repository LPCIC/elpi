/*
 * Predicates for transforming formulas into prenex normal form 
 * assuming classical logic equivalences. This is an example of 
 * analyzing formula structure, including recursion over bindings
 * and generating modified structure based on this analysis
 */

module  pnf.

type  merge  (form -> form -> o).

(prenex B B) :- (quant_free B), !. 
(prenex (B and C) D) :- (prenex B U), (prenex C V), (merge (U and V) D).
(prenex (B or C) D) :- (prenex B U), (prenex C V), (merge (U or V) D).
(prenex (B imp C) D) :- (prenex B U), (prenex C V), (merge (U imp V) D).
(prenex (all B) (all D)) :- (pi X\ ((termp X) => (prenex (B X) (D X)))).

(prenex (some B) (some D)) :- (pi X\ ((termp X) => (prenex (B X) (D X)))).


/* This predicate is for moving out quantifiers appearing at the head of the 
immediate subformulas of a formula with a propositional connective as its 
top-level symbol */
(merge ((all B) and (all C)) (all D)) :-
       (pi X\ ((termp X) => (merge ((B X) and (C X)) (D X)))).
(merge ((all B) and C) (all D)) :- 
       (pi X\ ((termp X) => (merge ((B X) and C) (D X)))).
(merge (B and (all C)) (all D)) :- 
       (pi X\ ((termp X) => (merge (B and (C X)) (D X)))).

(merge ((some B) and C) (some D)) :- 
       (pi X\ ((termp X) => (merge ((B X) and C) (D X)))).
(merge (B and (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (B and (C X)) (D X)))).

(merge ((all B) or C) (all D)) :-
       (pi X\ ((termp X) => (merge ((B X) or C) (D X)))).
(merge (B or (all C)) (all D)) :-
       (pi X\ ((termp X) => (merge (B or (C X)) (D X)))).
(merge ((some B) or (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge ((B X) or (C X)) (D X)))).
(merge ((some B) or C) (some D)):-
       (pi X\ ((termp X) => (merge ((B X) or C) (D X)))).
(merge (B or (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (B or (C X)) (D X)))).

(merge ((all B) imp (some C)) (some D)) :- 
       (pi X\ ((termp X) => (merge ((B X) imp (C X)) (D X)))).
(merge ((all B) imp C) (some D)) :- 
       (pi X\ ((termp X) => (merge ((B X) imp C) (D X)))).
(merge ((some B) imp C) (all D)) :-
       (pi X\ ((termp X) => (merge ((B X) imp C) (D X)))).
(merge (B imp (all C)) (all D)) :-
       (pi X\ ((termp X) => (merge (B imp (C X)) (D X)))).
(merge (B imp (some C)) (some D)) :-
       (pi X\ ((termp X) => (merge (B imp (C X)) (D X)))).

(merge B B) :- (quant_free B).

