% 29 july 2014.
sig certificatesLKF.
accum_sig lkf-syntax.


type decide_ke					cert -> index -> cert -> o.
type release_ke 				cert -> cert -> o.
     
type store_kc					cert -> form -> index -> cert -> o.
type initial_ke					cert -> index -> o.
type all_kc					cert -> (A -> cert) -> o.
type some_ke					cert -> A -> cert -> o.
type andNeg_kc,	 andPos_ke			cert -> form -> cert -> cert -> o.
type andPos_k	 				cert -> form -> direction -> cert -> cert -> o.
type orNeg_kc 	 				cert -> form -> cert -> o.
type orPos_ke    	    			cert -> form -> choice -> cert -> o.
type true_ke 					cert -> o.
type false_kc 					cert -> cert -> o.

type cut_ke cert -> form -> cert -> cert -> o.
