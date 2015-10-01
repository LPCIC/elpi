module ex3.

accumulate arithmetic.
accumulate constructive_logic.

local ex3dummy osyn -> o.
ex3dummy X.

has_otype ex3 divides ((tuple_type [nat, nat]) arrow nat).
has_otype ex3 iff ((tuple_type [bool, bool]) arrow bool).

definition ex3 iff1 
	trueP
	(app iff (tuple [A, B]))
	(app and (tuple [(app imp (tuple [A, B])),
			 (app imp (tuple [B, A]))])).

definition ex3 divides1
	trueP
	(app divides (tuple [A, B]))
	(app exists (tuple [nat, (abs c\
		(app eq (tuple [B, (app otimes (tuple [A, c]))])))])).

top_goal ex3 divides_zero []
	(app forall (tuple [nat, (abs x\
		(app iff (tuple [
			(app divides (tuple [zero, x])),
			(app eq (tuple [x, zero]))])))])).

compound ex3 ex3_top_meth (complete_meth
		(repeat_meth
		(orelse_meth trivial
		(orelse_meth allFi
	 	(orelse_meth ex3_taut
            	(orelse_meth sym_eval
		(orelse_meth existential
		(orelse_meth (repeat_meth generalise)
                         (ind_strat normal_ind)
	))))))))
	_
	true.

compound ex3 ex3_taut
      (complete_meth
         (repeat_meth
           (orelse_meth trivial
            (orelse_meth false_e
            (orelse_meth all_imp_left
	   (orelse_meth neg_i
            (orelse_meth neg_e
            (orelse_meth imp_i
            (orelse_meth all_i
            (orelse_meth exists_i
            (orelse_meth and_i
            (orelse_meth and_e
            (orelse_meth or_e
            (orelse_meth imp_e1
            (orelse_meth imp_e2
            (orelse_meth imp_e3
            (orelse_meth imp_e4
            (orelse_meth or_il or_ir))))))))))))))))))
	_
	true.

atomic ex3 all_imp_left
        (seqGoal (H >>> (app imp 
                        (tuple [(app exists (tuple [QType, (abs P)])), Q]))))
        true
        true
        (seqGoal (H >>> (app forall (tuple [QType,
                        (abs X\ (app imp (tuple [(P X), Q])))]))))
        notacticyet.

dividesthm:-
	(sym_eval_list [iff1, divides1, plus1, plus2, times1, times2] =>
		pds_plan ex3_top_meth divides_zero).
	

end
	
