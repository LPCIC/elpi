module ex2.

accumulate objlists.
accumulate constructive_logic.

has_otype ex2 qrev ((tuple_type [(olist X), (olist X)]) arrow (olist X)).

definition ex2 qrev1 
	trueP
	(app qrev (tuple [onil, L]))
	L.
definition ex2 qrev2
	trueP
	(app qrev (tuple [(app ocons (tuple [H, T])), L]))
	(app qrev (tuple [T, (app ocons (tuple [H, L]))])).

lemma ex2 oapp_lemma equiv
	trueP
        (app oapp (tuple [(app qrev (tuple [L2, L3])), L4]))
        (app qrev (tuple [L2, (app oapp (tuple [L3, L4]))])).



top_goal ex2 orevqrev []
	(app forall (tuple [(olist nat), (abs x\
		(app forall (tuple [(olist nat), (abs y\
			(app eq (tuple [
	(app oapp (tuple [(app orev x), y])),
	(app qrev (tuple [x, y]))])))])))])).

top_goal ex2 revqrevlemma []
	(app forall (tuple [(olist nat), (abs x\
		(app forall (tuple [(olist nat), (abs y\
			(app forall (tuple [(olist nat), (abs z\
	(app eq (tuple [
	(app oapp (tuple [(app qrev (tuple [x, y])), z])),
	(app qrev (tuple [x, (app oapp (tuple [y, z]))]))])))])))])))])).

orevqrevplan:-
        (induction_schemes_list [list_struct] =>
                (sym_eval_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2, oapp_lemma] =>
                (wave_rule_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2, oapp_lemma] =>
                pds_plan (induction_top normal_ind) orevqrev))).

revqrevlemmaplan:-
        (induction_schemes_list [list_struct] =>
                (sym_eval_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2] =>
                (wave_rule_list [idty, cons_functional, orev1, orev2, oapp1, oapp2, qrev1, qrev2] =>
                pds_plan (induction_top normal_ind) revqrevlemma))).
end

