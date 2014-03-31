open Pcaml

IFDEF TRACE THEN
EXTEND
  expr:
     [ [ "TRACE"; c = expr LEVEL "simple"; e = expr LEVEL "simple"; b = SELF ->
         <:expr<
           do { 
             Trace.enter $c$ (lazy $e$);
             try let rc = $b$ in do { Trace.exit (); rc }
             with [ e when Trace.debug.val ->
                     do { Trace.exit ~e (); raise e } ] } >> ] ]
  ;
END
ELSE
EXTEND
  expr:
     [ [ "TRACE"; c = expr LEVEL "simple"; e = expr LEVEL "simple"; b = SELF ->
         <:expr< $b$ >> ]]
  ;
END
END
