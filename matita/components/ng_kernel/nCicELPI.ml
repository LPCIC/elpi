(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department, University of Bologna, Italy.                     
    ||I||                                                                
    ||T||  HELM is free software; you can redistribute it and/or         
    ||A||  modify it under the terms of the GNU General Public License   
    \   /  version 2 or (at your option) any later version.      
     \ /   This software is distributed as is, NO WARRANTY.     
      V_______________________________________________________________ *)

module U   = NUri
module R   = NReference
module C   = NCic
module P   = NCicPp
module E   = NCicEnvironment
module LPT = Elpi_trace
module LPA = Elpi_ast
module LPX = Elpi_latex_exporter (* initializes the parser, puah :( *)
module LPP = Elpi_parser
module LPR = Elpi_runtime
module LPC = Elpi_custom (* registers the custom predicates, if we need them *)

type kernel_t = NO | FG | CSC

type tag = SORT | PROD | ABST | ABBR | APPL | CASE

(* variables ****************************************************************)

let matita_dir = Filename.dirname (Sys.argv.(0))

let kernel = ref NO

let get_program kernel =
   let paths, filenames = match kernel with
      | NO  -> ["../.."; ], []
      | FG  -> ["../.."; "../../lib"; "../../bench/sources/cic"; ],
               ["debug_front.elpi";
                "kernel_matita.elpi";
                "kernel.elpi";
                "debug_end.elpi";
               ]
      | CSC -> ["../.."; "../../../papers/DALEFEST/elpi"; ],
               [ "trace_kernel.elpi";
                 "PTS_matita.elpi";
                 "PTS_kernel_machine.elpi";
                 "debug_kernel.elpi";
               ]
   in
   let paths = List.map (Filename.concat matita_dir) paths in
   LPR.program_of_ast (LPP.parse_program ~paths ~filenames)

let program = ref (get_program !kernel)

let current = ref None

(* internals ****************************************************************)

let xlate tag = match !kernel, tag with
   | NO , _    -> "??"
   | _  , SORT -> "sort"
   | FG , PROD -> "prod"
   | CSC, PROD -> "arr"
   | FG , ABST -> "abst"
   | CSC, ABST -> "lam"
   | _  , ABBR -> "abbr"
   | FG , APPL -> "appl"
   | CSC, APPL -> "app"
   | FG , CASE -> "case"
   | CSC, CASE -> "match"

let status = new P.status

let rt_gref r =
   let R.Ref (uri, spec) = r in
   let _, _, _, _, obj = E.get_checked_obj status uri in
   match obj, spec with 
      | C.Constant (_, _, None, u, _)  , R.Decl          ->
         None, u
      | C.Constant (_, _, Some t, u, _), R.Def h         ->
         Some (h, t), u
      | C.Fixpoint (true, fs, _)       , R.Fix (i, _, h) ->
         let _, _, _, u, t = List.nth fs i in
         Some (h, t), u
      | C.Fixpoint (false, fs, _)      , R.CoFix i       ->
         let _, _, _, u, _ = List.nth fs i in
         None, u
      | C.Inductive (_, _, us, _)      , R.Ind (_, i, _) ->
         let _, _, u, _ = List.nth us i in
         None, u
      | C.Inductive (_, _, us, _)      , R.Con (i, j, _) ->
         let _, _, _, ts = List.nth us i in
         let _, _, u = List.nth ts (pred j) in
         None, u
      | _                                                ->
         assert false

let split_constructor = function
   | R.Ref (_, R.Con (_, j, k)) -> Some (pred j, k)
   |_                           -> None

let split_inductive = function
   | R.Ref (_, R.Ind (_, _, k)) -> Some k
   |_                           -> None

let split_fixpoint = function
   | R.Ref (_, R.Fix (_, l, _)) -> Some l
   |_                           -> None

let id x = "u+" ^ x

let univ_of u =
   try Scanf.sscanf (U.string_of_uri u) "cic:/matita/pts/Type%s@.univ" id
   with Scanf.Scan_failure _ | End_of_file -> assert false

let mk_univ s =
   let cons = match s with
      | C.Prop             -> ["s+prop"]
      | C.Type []          -> ["s+type"; "u+0"]
      | C.Type [`Type, u]  -> ["s+type"; univ_of u]
      | C.Type [`CProp, u] -> ["s+cprop"; univ_of u]
      | _                  -> assert false (* for now we process just universes in normal form *)
   in
   LPA.mkApp (List.map LPA.mkCon cons)

let mk_nil = LPA.mkNil

let mk_cons v vs = LPA.mkSeq [v; vs]

let mk_head x = LPA.mkCon (xlate x)

let mk_name i = Printf.sprintf "x%u" i

let mk_lref c i = LPA.mkCon (mk_name (c - i))

let mk_gref r = LPA.mkCon (R.string_of_reference r)

let mk_sort s = LPA.mkApp [mk_head SORT; mk_univ s]

let mk_prod n w t = LPA.mkApp [mk_head PROD; w; LPA.mkLam (mk_name n) t]

let mk_abst n w t = LPA.mkApp [mk_head ABST; w; LPA.mkLam (mk_name n) t]

let mk_abbr n v w t = match !kernel with
   | NO | FG -> LPA.mkApp [mk_head ABBR; v; w; LPA.mkLam (mk_name n) t]
   | CSC     -> LPA.mkApp [mk_head ABBR; w; v; LPA.mkLam (mk_name n) t]

let mk_appl t v = LPA.mkApp [mk_head APPL; t; v]

let mk_case w v u ts = LPA.mkApp [mk_head CASE; w; u; v; ts]

let mk_is_type u = LPA.mkApp [LPA.mkCon "is_type"; u]

let mk_has_type t u = LPA.mkApp [LPA.mkCon "has_type"; t; u]

(* matita to elpi *)
let rec lp_term c = function
   | C.Meta _
   | C.Implicit _          -> assert false (* for now we process just closed terms *)
   | C.Rel i               -> mk_lref c i
   | C.Const r             -> mk_gref r
   | C.Sort s              -> mk_sort s
   | C.Prod (_, w, t)      -> mk_prod c (lp_term c w) (lp_term (succ c) t)
   | C.Lambda (_, w, t)    -> mk_abst c (lp_term c w) (lp_term (succ c) t)
   | C.LetIn (_, w, v, t)  -> mk_abbr c (lp_term c v) (lp_term c w) (lp_term (succ c) t)
   | C.Appl []             -> assert false
   | C.Appl [t]            -> lp_term c t
   | C.Appl (t :: vs) when !kernel <> CSC -> mk_appl (lp_term c t) (lp_terms c vs)
   | C.Appl [t; v]         -> mk_appl (lp_term c t) (lp_term c v)
   | C.Appl (t :: v :: vs) -> lp_term c (C.Appl (C.Appl [t; v] :: vs))
   | C.Match (r, u, v, ts) -> mk_case (mk_gref r) (lp_term c v) (lp_term c u) (lp_terms c ts)

and lp_terms c = function
   | []      -> mk_nil
   | v :: vs -> mk_cons (lp_term c v) (lp_terms c vs)

let mk_term ~depth t =
   LPR.term_of_ast ~depth (lp_term 0 t)

let mk_int ~depth i =
   LPR.term_of_ast ~depth (LPA.mkInt i)

let mk_eq t1 t2 = LPR.App (LPR.Constants.eqc, t1, [t2])

let show = LPR.Constants.show

let dummy = LPR.Constants.dummy

let fail () = raise LPR.No_clause

let rec get_gref ~depth = function
   | LPR.Const c                                                    ->
       if c >= 0 then fail () else R.reference_of_string (show c)
   | LPR.UVar ({LPR.contents=t;_},vardepth,args) when t != dummy    ->
      get_gref ~depth (LPR.deref_uv ~from:vardepth ~to_:depth args t)
   | LPR.AppUVar ({LPR.contents=t;_},vardepth,args) when t != dummy ->
      get_gref ~depth (LPR.deref_appuv ~from:vardepth ~to_:depth args t)
   | _                                                              -> fail ()

let get_gref f ~depth t =
   try f (get_gref ~depth t) with
      | Failure "nth"
      | Invalid_argument "List.nth"
      | R.IllFormedReference _
      | E.ObjectNotFound _
      | LPR.No_clause           -> fail ()

let get_type ~depth ~env:_ _ = function
   | [t1; t2] -> 
      begin match get_gref rt_gref ~depth t1 with
          | _, u1 -> [mk_eq (mk_term ~depth u1) t2]
      end
   | _        -> fail ()

let get_expansion ~depth ~env:_ _ = function
   | [t1; t2; t3] ->
      begin match get_gref rt_gref ~depth t1 with
          | Some (h, u1), _ -> [mk_eq (mk_int ~depth (-h)) t2; mk_eq (mk_term ~depth u1) t3]
          | _               -> fail ()
      end
   | _        -> fail ()

let get_constructor ~depth ~env:_ _ = function
   | [t1; t2; t3] -> 
      begin match get_gref split_constructor ~depth t1 with
          | Some (j, k) -> [mk_eq (mk_int ~depth j) t2; mk_eq (mk_int ~depth k) t3]
          | _           -> fail ()
      end
   | _            -> fail ()

let get_inductive ~depth ~env:_ _ = function
   | [t1; t2] -> 
      begin match get_gref split_inductive ~depth t1 with
          | Some j -> [mk_eq (mk_int ~depth j) t2]
          | _      -> fail ()
      end
   | _        -> fail ()

let get_fixpoint ~depth ~env:_ _ = function
   | [t1; t2] ->
      begin match get_gref split_fixpoint ~depth t1 with
          | Some l -> [mk_eq (mk_int ~depth l) t2]
          | _      -> fail ()
      end
   | _        -> fail ()

let on_object ~depth ~env:_ _ args = match args, !current with
   | [t1], Some t -> [mk_eq (mk_term ~depth t) t1]
   | _            -> fail ()

(* initialization ***********************************************************)

let _ =
   LPR.register_custom "$get_type" get_type;
   LPR.register_custom "$get_expansion" get_expansion;
   LPR.register_custom "$get_constructor" get_constructor;
   LPR.register_custom "$get_inductive" get_inductive;
   LPR.register_custom "$get_fixpoint" get_fixpoint;
   LPR.register_custom "$on_object" on_object

(* interface ****************************************************************)

let set_kernel e =
   kernel := e; program := get_program e

(* Note: to be replaced by String.uppercase_ascii *)
let set_kernel_from_string s = match String.uppercase s with
   | "NO"  -> set_kernel NO
   | "FG"  -> set_kernel FG
   | "CSC" -> set_kernel CSC
   | _     -> ()

let set_trace () =
   ignore (LPT.parse_argv [| "-perf-on"; "-trace-at"; "run"; "1"; "99999999" |])

let execute r query =
   let str = R.string_of_reference r in
   Printf.printf "?? %s\n%!" str;
   current := Some (C.Const r);
   let b = LPR.execute_once !program (LPR.query_of_ast !program query) in
   let result = if b then "KO" else "OK" in
   Printf.printf "%s %s\n%!" result str; b

let is_type r u =
   let query = mk_is_type (lp_term 0 u) in
   execute r query

let has_type r t u =
   let query = mk_has_type (lp_term 0 t) (lp_term 0 u) in
   execute r query
