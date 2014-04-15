(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)

open Pcaml

IFDEF TRACE THEN
EXTEND
  expr:
     [ [ "TRACE"; c = expr LEVEL "simple"; e = expr LEVEL "simple"; b = SELF ->
         <:expr<
           let wall_clock = Unix.gettimeofday () in
           do { 
             Trace.enter $c$ $e$;
             try
               let rc = $b$ in do {
               Trace.exit $c$( Unix.gettimeofday () -. wall_clock);
               rc }
             with [ e -> do {
               Trace.exit $c$ ~e (Unix.gettimeofday () -. wall_clock);
               raise e } ] } >> ]
     | [ "SPY"; n = expr LEVEL "simple"; c = expr LEVEL "simple";
                                         x = expr LEVEL "simple" ->
         <:expr< Trace.print $n$ $c$ $x$ >> ]
     ]
  ;
END
ELSE
EXTEND
  expr:
     [ [ "TRACE"; c = expr LEVEL "simple"; e = expr LEVEL "simple"; b = SELF ->
         <:expr< $b$ >> ]
     | [ "SPY"; n = expr LEVEL "simple"; c = expr LEVEL "simple";
                                         x = expr LEVEL "simple" ->
         <:expr< () >> ]
     ]
  ;
END
END
