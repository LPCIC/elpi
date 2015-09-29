module ex1.

accumulate objlists.
accumulate constructive_logic.

has_otype ex1 qrev ((tuple_type [(olist X), (olist X)]) arrow (olist X)).

definition ex1 qrev1 
	trueP
	(app qrev (tuple [onil, L]))
	L.
definition ex1 qrev2
	trueP
	(app qrev (tuple [(app ocons (tuple [H, T])), L]))
	(app qrev (tuple [T, (app ocons (tuple [H, L]))])).

top_goal ex1 orevqrev []
	(app forall (tuple [(olist nat), (abs x\
		(app forall (tuple [(olist nat), (abs y\
			(app eq (tuple [
	(app oapp (tuple [(app orev x), y])),
	(app qrev (tuple [x, y]))])))])))])).
end