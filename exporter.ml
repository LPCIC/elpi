(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)


module Export = struct
(* ------ LaTeX exporter ------- *)

(* if  q :- a,b,c  returns a pair (q,[a;b;c]) *)
let clausify t = match t with
  | Parser.App(Parser.Const f,tl) ->
     (match tl with
        | [left;right] when Parser.ASTFuncS.pp f = (Parser.ASTFuncS.pp Parser.ASTFuncS.rimplf) ->
            let rec hyps andl = (match andl with
              | Parser.App(Parser.Const f,conjl) when Parser.ASTFuncS.pp f = (Parser.ASTFuncS.pp Parser.ASTFuncS.andf) -> (match conjl with
                  | x::y::nil -> x :: (hyps y) 
                  | _ -> assert false) 
              | _ -> [andl] ) in             
            let right = hyps right in
            (left,right)
        | _ -> (t,[])) 
  | _ -> (t,[])          
   
let cnt = ref 0 

(*x\ f x is transformed to v1\ f v1, where v1 is fresh*)
let rename_bound_var lambda =
 (* strings such as "open\_in", "\$print" are illegal in ocaml.
    How to export them in LaTeX ? *)
 (* let rename (str:string) = 
    let l = Str.split (Str.regexp "[_]") str in
    let s = List.fold_left (fun res x->res ^ "\\_" ^ x) "" (List.tl l) in 
    (List.hd l) ^ s in *)
  let rec subst t v newv = match t with
    | Parser.Const(v1) when v = v1 -> Parser.Const newv
    | Parser.Custom(v1) when v = v1 -> Parser.Custom newv
    | Parser.App(t1,tl) ->
       let newtl = List.map (fun x -> subst x v newv) tl in
       Parser.App(t1,newtl)
    | Parser.Lam(v1,tm) when v = v1 -> Parser.Lam(newv,subst tm v newv)
    | Parser.Lam(v1,tm) -> Parser.Lam(v1,subst tm v newv)
    | _ -> t in
  match lambda with
    | Parser.Lam(v,_) -> 
        incr cnt; subst lambda v (Parser.ASTFuncS.from_string ("v_{" ^ (string_of_int !cnt) ^ "}"))
    | _ -> lambda


(* (q,[a; b=>c; d; pi x\ (f x)] returns 
     ([(None,a);(b,c);(None,d);(None,f x)], [x])*)
let create_context pairsl =
  let fresh_vars = ref [] in 
  let rec aux = function
  | [] -> []
  | (Parser.App(Parser.Const f,tl) as fla)::rest -> (match tl with
      | [left;right] when Parser.ASTFuncS.pp f = (Parser.ASTFuncS.pp Parser.ASTFuncS.implf) -> (Some left,right) :: (aux rest)
      | [Parser.Lam(_,_) as lam] when Parser.ASTFuncS.pp f = (Parser.ASTFuncS.pp Parser.ASTFuncS.pif) ->
          let newlam = rename_bound_var lam in
          (match newlam with
            | Parser.Lam(v,t) -> 
                fresh_vars := !fresh_vars @ [Parser.Const v]; 
                let pair_t = List.hd (aux [t]) in
                pair_t :: (aux rest)
            | _ -> assert false )
      | _ -> (None,fla) :: (aux rest) ) 
  | hd::rest -> (None,hd) :: (aux rest) in
  (aux (snd pairsl),!fresh_vars) 
  
  


(* exports a f-la occurrence, i.e. q,a,b,c f-las from above *)
let rec export_term = function
   Parser.Const f 
 | Parser.Custom f -> Parser.ASTFuncS.pp f
 | Parser.App(f,tl) -> 
    (match tl with
      [] -> export_term f
    | [x] -> 
       if (export_term f) == (Parser.ASTFuncS.pp Parser.ASTFuncS.pif) then
        match x with
          Parser.Lam(_,_) ->  "(" ^ " \\forall " ^ (export_term x) ^ ")"
        | _ -> assert false 
       else
        (export_term f) ^ "(" ^ (export_term x) ^ ")"
    | [x;y] -> 
       if (export_term f) == (Parser.ASTFuncS.pp Parser.ASTFuncS.eqf) then
        "(" ^ (export_term x) ^ " = " ^ (export_term y) ^ ")"
       else if (export_term f) == (Parser.ASTFuncS.pp Parser.ASTFuncS.implf) then
        "(" ^  (export_term x) ^ " \\rightarrow " ^ (export_term y) ^ ")" 
       else if (export_term f) == (Parser.ASTFuncS.pp Parser.ASTFuncS.andf) then
         "(" ^ (export_term x) ^ " \\wedge " ^ (export_term y) ^ ")"
       else if (export_term f) == (Parser.ASTFuncS.pp Parser.ASTFuncS.orf) then
         "(" ^ (export_term x) ^ " \\vee " ^ (export_term y) ^ ")"
       else (export_term f) ^ "(" ^ (export_term x) ^ "," ^ (export_term y) ^ ")"
    | _ -> let last,tail = (List.hd (List.rev tl)), (List.rev (List.tl (List.rev tl))) in
      (export_term f) ^ "(" ^ (List.fold_left (fun l x -> l^(export_term x)^",") "" tail) ^ (export_term last) ^ ")" ) 
 | Parser.Lam (x,t1) ->
    " \\lambda "^ Parser.ASTFuncS.pp x^"." ^ (export_term t1)
 | Parser.String str -> Parser.ASTFuncS.pp str
 | Parser.Int i -> string_of_int i 
 | Parser.Float i -> string_of_float i 


(* exports b => c, i.e. (b,c) to b |- c*)
let export_pair = function
  | (None,b) -> " \\Gamma\\vdash " ^ export_term b
  | (Some a,b) -> " \\Gamma," ^ export_term a ^" \\vdash "^  export_term b


let export_clauses cl_list = 
 let headers = 
  "\\documentclass[10pt]{article} 

\\usepackage[utf8]{inputenc}
\\usepackage{amssymb}
\\usepackage{color}
\\usepackage{bussproofs}

\\begin{document} \n\n" in
 let rules = List.fold_left (fun l cl ->
   let clpair = clausify cl in
   let create_pairs = create_context clpair in
   let fst_ = fst create_pairs in
   let snd_ = snd create_pairs in
   let fresh_str = match snd_ with
     | [] -> ""
     | _ -> "fresh: " in
   let label = "\\RightLabel{" ^ fresh_str ^ "$" ^ 
                 (List.fold_right (fun freshvar l1 -> 
                  (export_term freshvar) ^ "," ^ l1) snd_ "" ) ^ 
                 "$}\n" in
   let arity = List.length (snd clpair) in
   let rule = match arity with
     | 0 -> "\\AxiomC{$$}\n" ^ "\\UnaryInfC{$" ^ (export_term (fst clpair))  ^ "$}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 1 -> label ^  "\\UnaryInfC{$" ^ (export_pair (None,fst clpair))  ^ "$}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 2 -> label ^ "\\BinaryInfC{$" ^ (export_pair (None,fst clpair))  ^ "$}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 3 -> label ^ "\\TrinaryInfC{$" ^ (export_pair (None,fst clpair))  ^ "$}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 4 -> label ^ "\\QuaternaryInfC{$" ^ (export_pair (None,fst clpair))  ^ "$}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 5 -> label ^ "\\QuinaryInfC{$" ^ (export_pair (None,fst clpair))  ^ "$}\n" ^ "\\DisplayProof\\newline\\newline\n\n" 
     | _ -> Format.printf "\nThe branching factor is > 5!\n%!"; 
            assert false in
   let axioms = List.fold_right (fun cl1 l1 -> "\\AxiomC{$" ^ (export_pair cl1) ^ "$}\n" ^ l1 ) fst_ "" in
   axioms ^ rule ^ l ) "" cl_list in
 let str = headers ^ rules ^ "\\end{document}" in
 Format.printf "%s%!" str;
 exit 1;

end
