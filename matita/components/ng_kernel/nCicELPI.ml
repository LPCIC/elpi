module U   = NUri
module R   = NReference
module C   = NCic
module LPA = Elpi_ast
module LPR = Elpi_runtime

let id x = x

let type_of u =
   try Scanf.sscanf (U.string_of_uri u) "cic:/matita/pts/Type%s@.univ" id
   with Scanf.Scan_failure _ | End_of_file -> assert false

let cprop_of u =
   try Scanf.sscanf (U.string_of_uri u) "cic:/matita/pts/CProp%s@.univ" id
   with Scanf.Scan_failure _ | End_of_file -> assert false

let string_of_sort = function
   | C.Prop             -> "prop_0"
   | C.Type []          -> "type_0"
   | C.Type [`Type, u]  -> Printf.sprintf "type_%s" (type_of u)
   | C.Type [`CProp, u] -> Printf.sprintf "crop_%s" (cprop_of u)
   | _                  -> assert false (* for now we process just universes in normal form *)

let mk_nil = LPA.mkNil

let mk_cons v vs = LPA.mkSeq [v; vs]

let mk_lref c i =
   try LPA.mkCon (List.nth c (pred i))
   with Not_found -> assert false

let mk_gref r = LPA.mkCon (R.string_of_reference r)

let mk_sort s = LPA.mkApp [LPA.mkCon "sort"; LPA.mkCon (string_of_sort s)]

let mk_prod n w t = LPA.mkApp [LPA.mkCon "prod"; w; LPA.mkLam n t]

let mk_abst n w t = LPA.mkApp [LPA.mkCon "abst"; w; LPA.mkLam n t]

let mk_abbr n v w t = LPA.mkApp [LPA.mkCon "abst"; v; w; LPA.mkLam n t]

let mk_appl t vs = LPA.mkApp [LPA.mkCon "appl"; t; vs]

let mk_case v u ts = LPA.mkApp [LPA.mkCon "case"; v; u; ts]

(* matita to elpi *)
let rec lp_term c = function
   | C.Meta _
   | C.Implicit _          -> assert false (* for now we process just closed terms *)
   | C.Rel i               -> mk_lref c i
   | C.Const r             -> mk_gref r
   | C.Sort s              -> mk_sort s
   | C.Prod (n, w, t)      -> mk_prod n (lp_term c w) (lp_term (n::c) t)
   | C.Lambda (n, w, t)    -> mk_abst n (lp_term c w) (lp_term (n::c) t)
   | C.LetIn (n, w, v, t)  -> mk_abbr n (lp_term c v) (lp_term c w) (lp_term (n::c) t)
   | C.Appl (t :: vs)      -> mk_appl (lp_term c t) (lp_terms c vs)
   | C.Appl []             -> assert false
   | C.Match (_, u, v, ts) -> mk_case (lp_term c v) (lp_term c u) (lp_terms c ts)

and lp_terms c = function
   | []      -> mk_nil
   | v :: vs -> mk_cons (lp_term c v) (lp_terms c vs)

let _ =
   Printf.printf "LP.register_custom\n%!";
   LPR.register_custom "$pippo" (fun ~depth:_ ~env:_ _ ts -> ts)
