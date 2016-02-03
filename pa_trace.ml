(* elpi: embedded lambda prolog interpreter                                  *)
(* copyright: 2014 - Enrico Tassi <enrico.tassi@inria.fr>                    *)
(* license: GNU Lesser General Public License Version 2.1                    *)

open Pcaml

IFDEF TRACE THEN
EXTEND
  expr:
    [[ "TRACE"; c = expr LEVEL "simple"; e = expr LEVEL "simple"; b = SELF ->
       <:expr<
       let wall_clock = Unix.gettimeofday () in do { 
       Trace.enter $c$ $e$;
       try
         let rc = $b$ in do {
         Trace.exit $c$ False (Unix.gettimeofday () -. wall_clock);
         rc }
       with [
         Trace.TREC_CALL(f,x) -> do { 
         Trace.exit $c$ True (Unix.gettimeofday () -. wall_clock);
         Obj.obj f (Obj.obj x) }
       | e -> do {
         Trace.exit $c$ False ~{e} (Unix.gettimeofday () -. wall_clock);
         raise e } ] } >> ]
    |[ "TCALL"; l = LIST1 expr LEVEL "simple" ->
       let l_rev = List.rev l in
       let last, pappl_rev = List.hd l_rev, List.tl l_rev in
       let pappl = List.rev pappl_rev in
       let func, args = List.hd pappl, List.tl pappl in
       let papp =
         List.fold_left (fun acc x -> MLast.ExApp(loc,acc,x)) func args in
       <:expr< raise (Trace.TREC_CALL(Obj.repr $papp$, Obj.repr $last$)) >> ]
    |[ "SPY"; n = expr LEVEL "simple"; c = expr LEVEL "simple";
                                       x = expr LEVEL "simple" ->
       <:expr< Trace.print $n$ $c$ $x$ >> ]
    ]
  ;
END
ELSE
EXTEND
  expr:
     [ [ "TRACE";
          c = expr LEVEL "simple"; e = expr LEVEL "simple"; b = SELF ->
         <:expr< $b$ >> ]
     |[ "TCALL"; l = LIST1 expr LEVEL "simple" ->
         let e = List.fold_left (fun acc x -> MLast.ExApp(loc,acc,x))
           (List.hd l) (List.tl l) in
         e ]
     | [ "SPY"; n = expr LEVEL "simple"; c = expr LEVEL "simple";
                                         x = expr LEVEL "simple" ->
         <:expr< () >> ]
     ]
  ;
END
END
