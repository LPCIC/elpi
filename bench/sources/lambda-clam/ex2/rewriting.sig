/*

File: rewriting.sig
Author: Louise Dennis / James Brotherston
Description: Methods for Symbolic Evaluation.
Last Modified: 15th July 2002

*/

sig rewriting.

accum_sig embed.

type rewriting theory.

%---------------------------------------------
% Method Names
%---------------------------------------------

type sym_eval           meth.
type general_rewriting  meth.
type rewrite_with      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_case_split      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_with_hyp   meth.
type deploy_lemma       rewrite_rule -> meth.
type unfold_defn        rewrite_rule -> meth. 


%---------------------------------------------

type unpolarise osyn -> osyn -> o.
type multiply_polarities polarity -> polarity -> polarity -> o.


/*  Main rewriting predicates */

%  to allow one-step rewriting with specified rules;
%  second argument is the rule actually used

type rewrite_with_rules (list rewrite_rule) -> rewrite_rule ->
                         osyn -> osyn -> osyn -> o.

type rewr rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o.  

type trivial_condition osyn -> (list osyn) -> o.

type bad_for_synthesis rewrite_rule -> osyn -> o.

type rewrite_using osyn -> osyn -> osyn -> mkey -> o.
type rewrite_using_prop osyn -> osyn -> osyn -> o. 

type congr (rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o) ->
            rewrite_rule -> polarity -> osyn -> osyn -> osyn -> o. 

type casesplit_analysis (list osyn) -> osyn -> rewrite_rule -> (list osyn) -> (list rewrite_rule -> o) -> o.
  

/* Support for qed command */

kind reasontype type.
type fwd reasontype.
type bwd reasontype.
   
type goal_to_lemma reasontype -> query -> theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.       

   

end
