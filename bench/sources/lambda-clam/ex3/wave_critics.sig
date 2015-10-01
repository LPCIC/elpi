/*

File: wave_critics.sig
Author: Louise Dennis / James Brotherston
Description: Induction engine including Andrew Ireland's critics
Last Modified: 21st August 2002

*/

sig wave_critics.

%% The signature for the induction engine is the signature for the 
%% logic_eq_constants module, which also contains various pretty-printing 
%% and syntax declarations, plus the signature for the pairing type, plus 
%% various things from the modules which do rewriting, induction and so on.

accum_sig logic_eq_constants, pairs.

%% From module: generalise

type gen         theory.
type generalise	 meth.

%% From module: embeds

type embeds      etree -> osyn -> osyn -> o.

%% From module: rewriting

type rewriting   theory.

type sym_eval           meth.
type general_rewriting  meth.
type rewrite_with      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_case_split      (list rewrite_rule -> o) -> rewrite_rule -> meth.
type rewrite_with_hyp   meth.
type deploy_lemma       rewrite_rule -> meth.
type unfold_defn        rewrite_rule -> meth. 

type trivial_condition  osyn -> (list osyn) -> o.
type bad_for_synthesis  rewrite_rule -> osyn -> o.

kind reasontype type.
type fwd        reasontype.
type bwd        reasontype.
   
type goal_to_lemma reasontype -> query -> theory -> rewrite_rule -> direction -> osyn -> osyn -> osyn -> o.          

%% From module: schemes

type measured       osyn -> (osyn -> osyn) -> osyn.
type free           osyn -> (osyn -> osyn) -> osyn.

%% From module: wave

type wave theory.

kind ripFail type.

type wave_method      dir -> rewrite_rule ->  meth.
type wave_case_split  rewrite_rule -> meth.

type check_wave_case_split rewrite_rule -> crit.
type wave_critic_strat crit.
type wave_patch        ripFail -> (list int) -> rewrite_rule -> crit.
type wave_failure      ripFail -> rewrite_rule -> crit.

type ripple_rewrite mkey -> rewrite_rule -> (list osyn) -> (pairing osyn (list etree)) -> (pairing osyn (list etree)) -> osyn -> (list int) -> o.

type sinkable etree -> o.

type embeds_list (list etree) -> (list osyn) -> osyn -> (list osyn) -> (list etree) -> (list etree) -> (list etree) -> o.
type   measure_check mkey -> dir -> (list etree) -> (list etree)  -> (list int) -> (list etree) -> (list osyn) -> (list osyn) -> o.

type strip_forall_embeds osyn -> etree -> osyn -> osyn -> o.

type ind_hyp hyp_ann.
type induction_hypothesis (list osyn) -> (list osyn) -> o.

type set_up_ripple     meth.   % meta-level step (find embedding)
type post_ripple       meth.   % meta-level step (throw away embedding)

%% From module: pwf

type pwf theory.

type piecewise_fertilisation meth.
type imp_ifert meth.


%% From module: induction

type induction theory.

kind indtype type.

type normal_ind   indtype.
type with_critics indtype.
type whisky_ind   indtype.

type induction_meth        indtype -> scheme -> subst ->  meth.
type fertilise             meth.
type fertilisation_strong  meth.
type fertilisation_weak    meth.
type truegoalmeth	     meth.

type induction_top indtype -> meth.
type ind_strat     indtype -> meth.
type step_case     indtype -> meth.

type trivials           meth.
type equality_condition meth.

type triv_abs rewrite_rule.

type sink_match_     osyn -> osyn -> osyn -> o.

%% NB: nothing required from module: casesplit

%% From this module

type induction_revision   meth -> (list int) -> crit.	
type generalisation_AI    etree -> osyn -> osyn -> crit.

type introduce_lemma osyn -> meth.
type introduce_gen   osyn -> meth.

type fun_iter     osyn.
type fun_compose  osyn.
type nat          osyn.

type previous_casesplit rewrite_rule -> crit.


end
