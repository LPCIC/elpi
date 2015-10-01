/*

File: arithmetic.mod
Author: Louise Dennis
Description: Theory of Natural Numbers
Last Modified: 20th March 2000

*/

module arithmetic.

accumulate mathweb.
accumulate lclam.

/* SYNTAX CONSTANTS */

is_otype arithmetic nat [zero] [s].

has_otype arithmetic zero nat.
has_otype arithmetic s (nat arrow nat).
has_otype arithmetic plus ((tuple_type [nat, nat]) arrow nat).
has_otype arithmetic minus ((tuple_type [nat, nat]) arrow nat).
has_otype arithmetic otimes ((tuple_type [nat, nat]) arrow nat).
has_otype arithmetic exp ((tuple_type [nat, nat]) arrow nat).
has_otype arithmetic leq ((tuple_type [nat, nat]) arrow bool).
has_otype arithmetic half (nat arrow nat).
has_otype arithmetic double (nat arrow nat).
has_otype arithmetic even (nat arrow bool).
has_otype arithmetic fun_compose ((tuple_type [(A arrow B), (C arrow A)]) arrow (C arrow B)).
has_otype arithmetic fun_iter ((tuple_type [nat, (A arrow A)]) arrow (A arrow A)).

%% the OpenMath phrasebook entries for the symbols:
%%================================================
print_open_math_ zero   "'OMI'(0)".
print_open_math_ plus   "'OMS'(name: \"plus\" cd: \"arith1\")".
print_open_math_ minus  "'OMS'(name: \"minus\" cd: \"arith1\")".
print_open_math_ otimes "'OMS'(name: \"times\" cd: \"arith1\")".
print_open_math_ exp    "'OMS'(name: \"power\" cd: \"arith1\")".
print_open_math_ leq    "'OMS'(name: \"leq\" cd: \"relation1\")".
        
print_open_math_ (app s B) String:- 
        pprint_string "***********************************",
        pprint_string "handling succesor function",
        print_open_math B Argument,
        String is "'OMA'('OMS'(name: \"plus\" cd: \"arith1\") [" ^ Argument ^ " 'OMI'(1)])".


has_otype arithmetic pred (nat arrow nat).
definition arithmetic pred1
	trueP
	(app pred zero)
	zero.
definition arithmetic pred2
	trueP
	(app pred (app s X))
	X.

% Basic rewrites
%

lemma arithmetic neq_zero_s equiv trueP (app eq (tuple [zero, (app s _)])) 
                                        falseP.
lemma arithmetic neq_s_zero equiv trueP (app eq (tuple [(app s _), zero])) 
                                        falseP.


% plus
%
definition arithmetic plus1 trueP (app plus (tuple [zero, Y])) Y.
definition arithmetic plus2 trueP
     (app plus (tuple [(app s Y), X])) 
     (app s (app plus (tuple [Y, X]))).


% times
%
definition arithmetic times1 trueP
   (app otimes (tuple [zero, _])) 
   zero.
definition arithmetic times2 trueP
   (app otimes (tuple [(app s Y), X])) 
   (app plus (tuple [(app otimes (tuple [Y, X])), X])).

% exp
%
definition arithmetic exp1 trueP
   (app exp (tuple [_, zero])) 
   (app s zero).
definition arithmetic exp2 trueP
   (app exp (tuple [X, (app s Y)])) 
   (app otimes (tuple [X, (app exp (tuple [X, Y]))])).

% s_functional
%
lemma arithmetic s_functional equiv trueP
   (app eq (tuple [(app s X), (app s Y)])) 
   (app eq (tuple [X, Y])).

% leq
%
% also not clear on definition/lemma distinction here
axiom arithmetic leq1 equiv trueP
   (app leq (tuple [zero, _Y]))
   trueP.
axiom arithmetic leq2 equiv trueP
   (app leq (tuple [(app s _), zero]))
   falseP.
axiom arithmetic leq_ss equiv trueP
   (app leq  
    (tuple [(app s X),
          (app s Y)])) 
   (app leq (tuple [X, Y])).
lemma arithmetic leq_transitive equiv 
	trueP
	(app transitive leq)
	trueP.

% half
%
definition arithmetic half1 trueP
(app half zero)
zero.

definition arithmetic half2 trueP
(app half (app s zero))
zero.

definition arithmetic half3 trueP
(app half (app s (app s X)))
(app half X).

% double
%
definition arithmetic double1 trueP
(app double zero)
zero.

definition arithmetic double2 trueP
(app double (app s X))
(app s (app s (app double X))).

% even
%
definition arithmetic even1 trueP
(app even zero)
trueP.

definition arithmetic even2 trueP
(app even (app s zero))
falseP.

definition arithmetic even3 trueP
(app even (app s (app s X)))
(app even X).

definition arithmetic fun_iter1 
	trueP
	(app fun_iter (tuple [zero, F]))
	(abs x\ x).
definition arithmetic fun_iter2
	trueP
	(app F (app (app fun_iter (tuple [N, F])) Z))
	(app (app fun_iter (tuple [(app s N), F])) Z).
definition arithmetic fun_iter3
	trueP
	(app F (app (app fun_iter (tuple [N, (abs x\ (app F x))])) Z))
	(app (app fun_iter (tuple [(app s N), (abs x\ (app F x))])) Z).

axiom arithmetic fun_compose1 equiv
	trueP
	(app (app fun_compose (tuple [F, G])) X)
	(app F (app G X)).
bad_for_synthesis fun_compose1 (app F _):-
        headvar_osyn F.


has_otype arithmetic less ((tuple_type [nat, nat]) arrow bool).
axiom arithmetic less1 equiv
	trueP
	(app less (tuple [X, zero]))
	falseP.
axiom arithmetic less2 equiv
	trueP
	(app less (tuple [zero, (app s X)]))
	trueP.
axiom arithmetic less3 equiv
	trueP
	(app less (tuple [(app s X), (app s Y)]))
	(app less (tuple [X, Y])).
lemma arithmetic less_transitive equiv 
        trueP
        (app transitive less)
        trueP.


%%
%% Constructor style schemes
%%

/*
% `
induction_scheme arithmetic s_to_ss_ind
   nat
   (dom (a\ (repl (app s a) (app s (app s a)))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [nat, (abs Prop)]))))
   % Step cases
   (
    (allGoal nat n\ (seqGoal (((hyp (otype_of n nat) nha)::
                               (hyp (Prop (app s n)) ind_hyp)::H)
			   >>>
			   (Prop (app s (app s n))))))
   % Base case
    **
	( (seqGoal (H >>> (Prop zero))) **
       (seqGoal (H >>> (Prop (app s zero)))))
	).
*/

% Structural induction for naturals
%
induction_scheme arithmetic nat_struct
   nat
   (dom (a \ (repl a (app s a))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [nat, (abs Prop)]))))
   % Step case
   (
    ((allGoal nat z\ (seqGoal ((hyp (otype_of z nat) nha)::(hyp (Prop z) ind_hyp)::H >>> (Prop (app s z))))))
   % Base case
    **
	(seqGoal (H >>> (Prop zero)))
	).

induction_scheme arithmetic twostep
   nat
   (dom (a\ (repl a (app s (app s a)))))
   (measured nat Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [nat, (abs Prop)]))))
   % Step cases
   (
    (allGoal nat n\ (seqGoal (((hyp (otype_of n nat) nha)::
                               (hyp (Prop n) ind_hyp)::H)
			   >>>
			   (Prop (app s (app s n))))))
   % Base case
    **
	( (seqGoal (H >>> (Prop zero))) **
       (seqGoal (H >>> (Prop (app s zero)))))
	).

% simple tautology
%
top_goal arithmetic eqzero [] (app eq (tuple [zero, zero])).
% simple tautology
%
top_goal arithmetic simple [] (app eq (tuple [zero, (app plus (tuple [zero, (app plus (tuple [zero,  zero]))]))])).

% simple tautology
%
top_goal arithmetic simple_taut [] (app imp (tuple [(app eq (tuple [zero, zero])), (app eq (tuple [zero, zero]))])).

% simple arithmetic 
%
top_goal arithmetic assp []
    (app forall (tuple [nat, 
     (abs z\ (app forall (tuple [nat, 
      (abs y\ (app forall (tuple [nat, 
       (abs x\ (app eq (tuple [
        (app plus (tuple [
         (app plus (tuple [x, y])), 
          z])), 
        (app plus (tuple [
         x, 
         (app plus (tuple [y, z]))]))])))])))])))])).

% simple arithmetic 
%
top_goal arithmetic comp []
     (app forall (tuple [nat,
      (abs x\ (app forall (tuple [nat, 
       (abs y\ (app eq (tuple [(app plus (tuple [y, x])),
                               (app plus (tuple [x, y]))])))])))])).

% simple arithmetic 
%
top_goal arithmetic comm []
     (app forall (tuple [nat,
      (abs x\ (app forall (tuple [nat, 
       (abs y\ (app eq (tuple [
        (app otimes (tuple [y, x])),
        (app otimes (tuple [x, y]))])))])))])).

% simple arithmetic, false
%
top_goal arithmetic falsearith []
	(app forall (tuple [nat, (abs x\ (app eq  (tuple [x, (app s x)])))])).

% simple arithmetic 
%
top_goal arithmetic plus2right []
	(app forall (tuple [nat,
         (abs y\ (app forall (tuple [nat,
	  (abs x\ (app eq (tuple [
           (app plus (tuple [x, (app s y)])),
           (app s (app plus (tuple [x, y])))])))])))])).

% simple arithmetic 
%
top_goal arithmetic dist []
   (app forall (tuple [nat,
    (abs x\ (app forall (tuple [nat,
     (abs y\ (app forall (tuple [nat,
      (abs z\ (app eq (tuple [
       (app otimes (tuple [x, (app plus (tuple [y, z]))])), 
       (app plus (tuple [
        (app otimes (tuple [x, y])),
        (app otimes (tuple [x, z]))]))])))])))])))])).

% simple arithmetic, different argument order from dist
%
top_goal arithmetic distr []
   (app forall (tuple [nat,
    (abs x\ (app forall (tuple [nat,
     (abs z\ (app forall (tuple [nat,
      (abs y\ (app eq (tuple [
       (app otimes (tuple [(app plus (tuple [y, z])), x])),
       (app plus (tuple [
        (app otimes (tuple [y, x])),
        (app otimes (tuple [z, x]))]))])))])))])))])).

% simple arithmetic, different argument order from dist
%
top_goal arithmetic assm []
   (app forall (tuple [nat,
    (abs z\ (app forall (tuple [nat,
     (abs y\ (app forall (tuple [nat,
      (abs x\ (app eq (tuple [
       (app otimes (tuple [(app otimes (tuple [x, y])), z])),
       (app otimes (tuple [x, (app otimes (tuple [y, z]))]))])))])))])))])).

% simple arithmetic synthesis proof, meta-variable for synthesised function.
%
top_goal arithmetic assp_sy []
     (app forall (tuple [nat,
      (abs x\ (app forall (tuple [nat,
       (abs y\ (app forall (tuple [nat,
        (abs z\ (app eq (tuple [
         (app plus (tuple [(app plus (tuple [x, y])), z])),  
         (app plus (tuple [x, (app W (tuple [x, y, z]))]))])))])))])))])).

% slightly more difficult arithmetic
%
top_goal arithmetic expplus []
    (app forall (tuple [nat,
     (abs z\ (app forall (tuple [nat,
      (abs x\ (app forall (tuple [nat,
       (abs y\ (app eq (tuple [
        (app exp (tuple [x, (app plus (tuple [y, z]))])),
        (app otimes (tuple [
         (app exp (tuple [x, y])), 
         (app exp (tuple [x, z]))]))])))])))])))])).

% slightly more difficult arithmetic
%
top_goal arithmetic exptimes []
    (app forall (tuple [nat,
     (abs n\ (app forall (tuple [nat,
      (abs m\ (app forall (tuple [nat,
       (abs o\ (app eq (tuple [
        (app exp (tuple [o, (app otimes (tuple [m, n]))])),
        (app exp (tuple [(app exp (tuple [o, m])), n]))])))])))])))])).

% For some reason called notleqreflex in CLAM corpus
%
top_goal arithmetic leqrefl []
   (app forall (tuple [nat,
    (abs n\ (app leq (tuple [n, n])))])).

% Arithmetic.
%
top_goal arithmetic leqsuc  []
    (app forall (tuple [nat,
       (abs n\ 
        (app leq  
           (tuple [n, 
                 (app s n)])))])).


top_goal arithmetic leqsum []
      (app forall (tuple [nat,
                (abs alpha\ (app forall (tuple [nat,
        (abs beta\ (app leq (tuple [alpha, (app plus (tuple [beta, alpha]))])))])))])).

top_goal arithmetic doublehalf []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [
			(app double (app half x)),
			x])))])).

top_goal arithmetic halfdouble []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [
			(app half (app double x)),
			x])))])).

top_goal arithmetic halfplus []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [
			(app half (app plus (tuple [x, x]))),
			x])))])).

top_goal arithmetic plus1lem []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [
			(app plus (tuple [x, (app s zero)])),
			(app s x)])))])).

top_goal arithmetic plusxx []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [
			(app plus (tuple [(app s x), x])),
			(app s (app plus (tuple [x, x])))])))])).

top_goal arithmetic zeroplus []
	(app forall (tuple [nat, (abs x\
		(app forall (tuple [nat, (abs y\
	(app imp (tuple [(app and (tuple [
				(app eq (tuple [x, zero])),
				(app eq (tuple [y, zero]))])),
			(app eq (tuple [(app plus (tuple [x, y])), zero]))])))])))])).

top_goal arithmetic zerotimes []
	(app forall (tuple [nat, (abs x\
		(app forall (tuple [nat, (abs y\
	(app imp (tuple [(app or (tuple [
				(app eq (tuple [x, zero])),
				(app eq (tuple [y, zero]))])),
			(app eq (tuple [(app otimes (tuple [x, y])), zero]))])))])))])).

top_goal arithmetic doubleplus []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [(app double x),
				(app plus (tuple [x, x]))])))])).

top_goal arithmetic doubletimes []
	(app forall (tuple [nat, (abs x\
		(app eq (tuple [(app double x),
				(app otimes (tuple [(app s (app s zero)), x]))])))])).

top_goal arithmetic times2right []
	(app forall (tuple [nat, (abs x\
		(app forall (tuple [nat, (abs y\
	(app eq (tuple [(app otimes (tuple [x, (app s y)])),
			(app plus (tuple [x, (app otimes (tuple [x, y]))]))])))])))])).

top_goal arithmetic doubletimes2 []
	  (app forall (tuple [nat, (abs x\
                (app eq (tuple [(app double x),
                                (app otimes (tuple [x, (app s (app s zero))]))])
))])).

%% Pretty printing

prettify_special zero (str "0").

end

