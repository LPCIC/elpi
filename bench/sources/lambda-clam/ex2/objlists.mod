/*

File: objlists.mod
Author: Louise Dennis
Description: A Theory for Lists
Last Modified: 20th March 2001

*/

module objlists.

accumulate arithmetic.

/*
local dummy1 X -> o.
dummy1 X:-
       printstdout X.
local dummy2 X -> o.
dummy2 X:-
       on_backtracking (printstdout X).
local dummy3 X -> o.
dummy3 X:-
       on_backtracking (printstdout X).
*/
% Basic rewrites
% 
lemma objlists cons_functional equiv trueP 
(app eq (tuple [(app ocons (tuple [X, Y])), (app ocons (tuple [W, Z]))])) 
(app and (tuple [(app eq (tuple [X, W])), (app eq (tuple [Y, Z]))])).

/*
lemma objlists neq_cons_nil equiv trueP 
(app eq (tuple [(app ocons (tuple [_, _])), onil])) falseP.
lemma objlists neq_nil_cons equiv trueP 
(app eq (tuple [onil, (app ocons (tuple [_, _]))])) falseP.
*/

definition objlists oapp1 trueP  (app oapp (tuple [onil, Y])) Y. 
definition objlists oapp2 trueP  (app oapp (tuple [(app ocons (tuple [X, Y])), Z])) (app ocons (tuple [X, (app oapp (tuple [Y, Z]))])).
lemma objlists ass_oapp equiv trueP  (app oapp (tuple [(app oapp (tuple [X, Y])), Z])) (app oapp (tuple [X, (app oapp (tuple [Y, Z]))])).


% olength
%
% (olength onil) => zero.
definition objlists olength1 trueP (app olength onil) zero.
%
% (olength (ocons H T)) => (s (olength T)). 
definition objlists olength2 trueP (app olength (app ocons (tuple [_H, T]))) (app s (app olength T)).

% orev - these need extra otype_of's on RHSs.
% '
% (orev onil) => onil
definition objlists orev1  trueP 
    (app orev onil ) 
    onil.
%
% (orev (ocons H T)) => (oapp (orev T) (ocons H onil)).
definition objlists orev2  trueP   
    (app orev (app ocons (tuple [H, T]))) 
    (app oapp (tuple [(app orev T),
                    (app ocons (tuple [H, onil]))])).


definition objlists allList1 trueP 
       (app allList (tuple [_X, onil])) 
       trueP.

definition objlists allList2 trueP 
       (app allList 
          (tuple [(abs X), (app ocons (tuple [H, T]))])) 
       (app and 
          (tuple [(X H), (app allList (tuple [(abs X), T]))])).

lemma  objlists allList_or_l rtol trueP 
     (app allList 
      (tuple [
       (abs (x\ (app or (tuple [(P x), (_Q x)])))), L]))
     (app allList (tuple [(abs P), L])).

lemma objlists allList_or_r rtol trueP 
     (app allList 
      (tuple [
       (abs (x\ (app or 
        (tuple [(_P x), (Q x)])))),
       L])) 
     (app allList (tuple [(abs Q), L])).



% Two step list induction
%
induction_scheme  objlists list_twostep
   % Info
   (olist T)
   (dom a\ (dom b\ (dom c\ (repl c (app ocons (tuple [a, (app ocons (tuple [b, c]))]))))))
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)]))))
   % Step cases
   (
    (allGoal (olist T) (t\ (allGoal T (h\ (allGoal T (i\ (seqGoal ((
		            (hyp (otype_of h T) nha)::
                            (hyp (otype_of i T) nha)::
                            (hyp (otype_of t (olist T)) nha)::
                            (hyp (Prop t) ind_hyp)::H)
                          >>>
                          (Prop (app ocons (tuple [h, (app ocons (tuple [i, t]))])))))))))))
   % Base case
    **
     ((seqGoal (H >>> (Prop onil)))
     ** 
     (allGoal T (s\ (seqGoal (((hyp (otype_of s T) nha)::H)
                           >>> (Prop (app ocons (tuple [s, onil] ))))))))
	).

% Structural induction for lists.
induction_scheme  objlists list_struct
   % Info
   (olist T)
   (dom (b \ (dom (c \ (repl c (app ocons (tuple [b, c])))))))
   (measured (olist T) Prop)
   % Goal
   (seqGoal (H >>> (app forall (tuple [(olist T), (abs Prop)]))))
   % Step case
   (
    (allGoal (olist T)
    t\ (allGoal T
    h\ (seqGoal (((hyp (otype_of h T) nha)::
               (hyp (otype_of t (olist T)) nha)::
               (hyp (Prop t) ind_hyp)::H)
          >>> (Prop (app ocons (tuple [h, t])))))))
    **
   % Base case
	(seqGoal (H >>> (Prop onil)))
	).






%
% Object level types
%

is_otype objlists (olist X) [onil] [ocons].

has_otype objlists onil (olist _X).
has_otype objlists ocons ((tuple_type [X, (olist X)]) arrow (olist X)).
has_otype objlists oapp ((tuple_type [(olist X), (olist X)]) arrow (olist X)). 
has_otype objlists olength ((olist _X) arrow nat). 
has_otype objlists orev    ((olist X) arrow (olist X)). 
has_otype objlists allList ((tuple_type [(X arrow bool), (olist X)]) arrow bool). 
% simple list theory
% 
top_goal objlists assapp []
     (app forall (tuple [(olist nat), (abs x\ (app forall (tuple [(olist nat),  (abs y\ (app forall (tuple [(olist nat), (abs z\ (app eq (tuple [(app oapp (tuple [(app oapp (tuple [x, y])),  z])),  (app oapp (tuple [x, (app oapp (tuple [y, z] ) )] ) )] )))])))])))])).

% next needs adjustments to rippling method.
%
% app_sy (forall (olist nat) l\ forall (olist nat) m\ (exists (olist nat) n\ 
%                (forall nat  x\ (((omember x l ) or (omember x m))))
%                                       (otype_of imp ((pair_type bool bool) arrow bool)) (omember x n) ) ).


% Higher-order in that it requires correct manipulation of lambda binders
% but does not really need any manipulation of the functions themselves.
% Ripples out 7 times then strong fertilises.
%
top_goal objlists all_list []
   (app forall (tuple [(nat arrow bool),
     (abs P\ (app forall (tuple [(nat arrow bool),
       (abs Q\ (app forall (tuple [(olist nat),
          (abs (l\ (app imp (tuple [
               (app and (tuple [
                      (app allList (tuple [(abs x\ (app P x)), l])),
                      (app allList (tuple [(abs x\ (app Q x)), l]))] )) ,
               (app allList (tuple [ 
                       (abs x\ (app and (tuple [(app P x), (app Q x)]))),
                        l]))] ))))])))])))])).

% Higher order and requires care with rewriting in the presence of a 
% meta-variable.
%
top_goal objlists all_list_sy []
   (app forall (tuple [(obj arrow bool),
    (abs P\ (app forall (tuple [(obj arrow bool),
     (abs Q\ (app exists (tuple [(obj arrow bool),
      (abs R\ (app forall (tuple [(olist obj),
       (abs l\ (app imp  
        (tuple [
         (app and  
          (tuple [
           (app allList  
            (tuple [P, l])),
           (app allList  
            (tuple [Q, l]))])), 
         (app allList  
          (tuple [R, l]))])) )])))])))])))])).

% all_list_u ( forall2 P\ (forall2 Q\ (forall (olist obj) l\ (
%    (((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool))P l) or ((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) Q l)) (otype_of imp ((pair_type bool bool) arrow bool)) 
%          ((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) (x\ ((P x) or (Q x))) l) )))).

% solved
%
top_goal objlists all_list_cv []
   (app forall (tuple [(obj arrow bool),
    (abs P\ (app forall (tuple [(obj arrow bool),
     (abs Q\ (app forall (tuple [(olist obj),
      (abs l\ (
         (app imp (tuple [
               (app allList (tuple [
                     (abs (x\ (app and (tuple [(app P x),
                                             (app Q x)])))), l])),
          (app and (tuple [(app allList (tuple [(abs x\ (app P x)), l])), 
                         (app allList (tuple [(abs x\ (app Q x)), l]))]))]))))]
              )))])))])).

%all_list_cv_sy ( (otype_of forall ((obj arrow bool) arrow bool)) P\ ((otype_of forall ((obj arrow bool) arrow bool)) Q\ exists2 R\ (forall (olist obj) l\ (((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) R l) (otype_of imp ((pair_type bool bool) arrow bool))
%                (((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) P l) (otype_of and ((pair_type bool bool) arrow bool)) ((otype_of allList ((pair_type (obj arrow bool) (olist obj)) arrow bool)) Q l))
%              )))).

% Three theorems from BBN 1163, section 3.
%
% solved
%
top_goal objlists allList_and_dist []
   (app forall (tuple [(obj arrow bool),
    (abs P\ (app forall (tuple [(obj arrow bool),
     (abs Q\ (app forall (tuple [(olist obj),
      (abs l\ 
       (app imp (tuple [ 
             (app allList (tuple [
                 (abs (x\ (app and (tuple [
                           (app P x), 
                           (app Q x)])))), 
                  l])),  
             (app and (tuple [
                  (app allList (tuple [(abs x\ (app P x)), l])),
                  (app allList (tuple [(abs x\ (app Q x)), l]))]))])))])))])))])).

% solved
%
top_goal objlists allList_and_dist_cv []
  (app forall (tuple [(obj arrow bool),
   (abs P\ (app forall (tuple [(obj arrow bool),
    (abs Q\ (app forall (tuple [(olist obj),
     (abs l\ 
      (app imp (tuple [(app and (tuple [(app allList (tuple [(abs x\ (app P x)), l])), 
                       (app allList (tuple [(abs x\ (app Q x)), l]))])), 
                 (app allList (tuple [(abs (x\ (app and (tuple [(app P x),
                                                                (app Q x)])))),
                                         l]))])))])))])))])).

% solved
%
top_goal objlists allList_or_left []
  (app forall (tuple [(obj arrow bool),
   (abs P\ (app forall (tuple [(obj arrow bool),
    (abs Q\ (app forall (tuple [(olist obj),
     (abs l\ (app imp 
      (tuple [ 
       (app allList 
        (tuple [(abs x\ (app P x)), l])), 
       (app allList  
        (tuple [
         (abs (x\ 
          (app or
           (tuple [ 
            (app P x), 
            (app Q x)])))), 
         l]))])))])))])))])).

% solved
%
top_goal objlists allList_or_right []
   (app forall (tuple [(obj arrow bool),
     (abs P\ (app forall (tuple [(obj arrow bool),
       (abs Q\ (app forall (tuple [(olist obj),
        (abs l\ (
            (app imp (tuple [(app allList (tuple [(abs x\ (app Q x)), l])), 
                           (app allList (tuple [
                                 (abs (x\ (app or (tuple [(app P x),
                                                        (app Q x)])))), 
                                          l]))]))))])))])))])).





end
