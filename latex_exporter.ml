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
        incr cnt; subst lambda v (Parser.ASTFuncS.from_string ("x{" ^ (string_of_int !cnt) ^ "}"))
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
 
(* the idea is to check if a meta-variable is applied to a fresh variable,
   i.e. if main :- (pi x\ G x ), H x, after removing pi we have:
   main :- G y, H x. The "y" is fresh and y \not \in FV(H) *)
let rec contains_var t v = match t with
 | Parser.Const f
 | Parser.Custom f ->
    (match v with 
     | Parser.Const sym -> Parser.ASTFuncS.pp f = Parser.ASTFuncS.pp sym 
     | _ -> assert false (* v should be a term: Const of ASTFuncS.t *))
 | Parser.App (Parser.Const hd,xs) -> 
    List.fold_left (fun rez x -> rez || (contains_var x v)) false xs 
 | Parser.Lam (_,t1) -> contains_var t1 v
 | _ -> false    

    
(* exports a f-la occurrence, i.e. q,a,b,c f-las from above *)
let export_term tm = 
  let rec aux prec t = match t with
    Parser.Const f 
  | Parser.Custom f -> 
     let name = Parser.ASTFuncS.pp f in 
     (try "<<>>" ^ (Parser.get_literal name) ^ "<<>>" with Not_found ->name)
        (* pp_app f ppconstant (aux max_int depth) (hd,xs) *)
  | Parser.App (Const hd,x::xs) ->
    (try
     let assoc,hdlvl = Parser.precedence_of hd in
     let lbracket,rbracket= if hdlvl < prec then ("(",")") else ("","") in
      lbracket ^
       (match assoc with
        | Parser.Infix when List.length xs = 1 ->
          (aux (hdlvl+1) x) ^ " " ^
          (aux 1000 (Const hd)) ^ " " ^
          (aux (hdlvl+1) (List.hd xs))
        | Parser.Infixl when List.length xs = 1 ->
          (aux hdlvl x) ^ " " ^
          (aux 1000 (Const hd)) ^ " " ^
          (aux (hdlvl+1)) (List.hd xs)
        | Parser.Infixr when List.length xs = 1 ->
          (aux (hdlvl+1) x) ^ " " ^
          (aux 1000 (Const hd)) ^ " " ^ 
          (aux hdlvl) (List.hd xs)
        | Parser.Prefix when xs = [] ->
          (aux 1000 (Const hd)) ^ " " ^
          (aux hdlvl x)
        | Parser.Postfix when xs = [] ->
          (aux hdlvl x) ^ " " ^
          (aux 1000 (Const hd)) 
        | _ -> (*"(" ^*) (aux 1001 (Const hd)) ^ " " ^
               (List.fold_left (fun l x -> l^(aux 1000 x)^(if (!cnt = 1) then "" else (decr cnt;" "))) "" (x::xs)) (*^ ")"*)) ^ rbracket
     with Not_found -> 
      let cnt = ref (List.length (x::xs)) in
      "(" ^ (aux 1001 (Const hd)) ^ " " ^
      (List.fold_left (fun l x -> l^(aux 1000 x)^(if (!cnt = 1) then "" else (decr cnt;" "))) "" (x::xs)) ^ ")") 

  | Parser.App (Custom hd,x::xs) ->
    (try
     let assoc,hdlvl = Parser.precedence_of hd in
      let lbracket,rbracket= if hdlvl < prec then ("(",")") else ("","") in
       (match assoc with
       | Parser.Infix when List.length xs = 1 ->
          (aux (hdlvl+1) x) ^ 
          (aux 1000 (Custom hd)) ^
          (aux (hdlvl+1) (List.hd xs))
       | Parser.Infixl when List.length xs = 1 ->
          (aux hdlvl x) ^
          (aux 1000 (Custom hd)) ^
          (aux (hdlvl+1)) (List.hd xs)
       | Parser.Infixr when List.length xs = 1 ->
          (aux (hdlvl+1) x) ^
          (aux 1000 (Custom hd)) ^
          (aux hdlvl) (List.hd xs)
       | Parser.Infixr when List.length xs = 1 ->
          (aux hdlvl x) ^
          (aux 1000 (Custom hd)) ^
          (aux (hdlvl+1)) (List.hd xs)
       | Parser.Prefix when xs = [] ->
          (aux 1000 (Custom hd)) ^
          (aux hdlvl x)
       | Parser.Postfix when xs = [] ->
          (aux hdlvl x) ^
          (aux 1000 (Custom hd))
       | _ -> "(" ^ (aux 1001 (Custom hd)) ^
          (List.fold_left (fun l x -> l^(aux 1000 x)^" ") "" (x::xs)) ^
           ")");
     with Not_found -> "(" ^ (aux 1001 (Const hd)) ^ " " ^
          (List.fold_left (fun l x -> l^(aux 1000 x)^" ") "" (x::xs)) ^")" )

(*
 | Parser.App(f,tl) -> 
    (match tl with
    | [] -> export_term prec f
    | [x] -> 
       if (export_term prec f) == (Parser.ASTFuncS.pp Parser.ASTFuncS.pif) then
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
      (export_term f) ^ "(" ^ (List.fold_left (fun l x -> l^(export_term x)^",") "" tail) ^ (export_term last) ^ ")" )  *)
  | Parser.Lam (x,t1) ->
     " lambda"^ Parser.ASTFuncS.pp x^"." ^ (aux prec t1)
  | Parser.String str -> Parser.ASTFuncS.pp str
  | Parser.Int i -> string_of_int i 
  | Parser.Float i -> string_of_float i in
 let pats =
  [ Str.regexp "\$", "\\$" (* for the custom predicates which start with $*)
  ; Str.regexp "<<>>",  "$" (* for mathematical mode in LaTeX, it is hidden from the user *)
  ; Str.regexp "_",  "\\_" (*for the _,otherwise exports it as a subscript*)
  ; Str.regexp "lambda", "$\\lambda$" ] in
 let new_tm = aux 0 tm in
 List.fold_left (fun s (a,b) -> Str.global_replace a b s) new_tm pats;;


(* exports b => c, i.e. (b,c) to b |- c*)
let export_pair = function
  | (None,b) -> "$ \\Gamma\\vdash $" ^ export_term b
  | (Some a,b) -> "$ \\Gamma,$" ^ export_term a ^" $\\vdash$ "^  export_term b


(*hd :- a,b,c  is the cl_pair (hd,[a,b,c])*)
let print_clause cl_pair =
 let rec print_fla f = match f with
  | Parser.Const c
  | Parser.Custom c -> Format.printf "%s%!" (Parser.ASTFuncS.pp c)
  | Parser.App(Parser.Const hd,tl)
  | Parser.App(Custom hd,tl) ->
     Format.printf "(%s %!" (Parser.ASTFuncS.pp hd);
     List.iter (fun x -> print_fla x; Format.printf " %!") tl;
     Format.printf ")%!";
  | Parser.Lam(x,t) ->
     Format.printf "λ%!";
     print_fla (Parser.Const x);
     Format.printf ".%!";
     print_fla t
  | _ -> Format.printf "not_important%!"; in
 print_fla (fst cl_pair);
 Format.printf " :- %!";
 List.iter (fun x -> (print_fla x); Format.printf ", %!";) (snd cl_pair);;


(* g F :- F a b  gives a eta-expanded clause, 
   i.e. the pair (f (\x\y. F) , F a b) *)
let eta_expand_clause cl = 
 let module FunctMap = Map.Make(Parser.ASTFuncS) in
 let arity_map = ref FunctMap.empty in
 (* adds the arity of a functor in the arity_map *) 
 let rec get_arity f = match f with
  | Parser.App(Parser.Const c, args) ->
     arity_map := FunctMap.add c (List.length args) !arity_map;
     List.iter (fun x -> get_arity x) args
  | Parser.App(Parser.Custom c, args) ->
     arity_map := FunctMap.add c (List.length args) !arity_map;
     List.iter (fun x -> get_arity x) args;
  | Parser.Lam(c,t) -> get_arity t
  | _ -> () in
 (* eta-exand f to its arity*)
 let rec add_lambdas f = match f with
  | Parser.Const c as name-> 
     (try let n = FunctMap.find c !arity_map in
     let rec aux i = (match i with
      | 0 -> [] 
      | _ -> 
        let var = Parser.ASTFuncS.from_string ("v" ^ (string_of_int i)) in
        var :: (aux (i-1))) in
     let varl = aux n in
     List.fold_left (fun rez x -> Parser.Lam(x,rez)) name varl
     with Not_found -> f) 
  | Parser.Lam(x,t) -> Parser.Lam(x,add_lambdas t) 
  | Parser.App(name,tl) -> 
     let tl = List.map (fun x -> add_lambdas x) tl in
     let newf = Parser.App(name, tl) in
     newf
  | _ -> f in
 let cl = clausify cl in
 List.iter (fun x -> get_arity x) ((fst cl)::(snd cl));
 let head = add_lambdas (fst cl) in
 let tail = List.map (fun f -> add_lambdas f) (snd cl) in
 (head,tail) 

(*from the pair ([(None,a);(b,H a);(None,F x)], [x,y]) where 
  [x,y] are the fresh vars, returns: 
   (Parser.term * (term list)) list
  The idea is that "x \not\in FV(H), 
  y \not\in FV(F,H)", i.e. [(x,[H a]),(y,[H a, F x]) *)
let not_in vars pairs = 
 let l = List.map (fun (x,y) -> 
  match x with 
   | Some z -> [z;y]
   | None -> [y]
  ) pairs in
 let l = List.flatten l in
 List.fold_left (fun rez v -> (v,(List.filter (fun x ->
   contains_var x v = false) l))::rez ) [] vars  

(*l: (variable * (term list)) list*)
let print_not_in l =
 let upper_case c = c >= 'A' && c <= 'Z' in
(* returns the meta-variables in term t *)
 let rec get_meta_vars t = match t with
  | Parser.Const c | Parser.Custom c -> 
   let name = Parser.ASTFuncS.pp c in
   if upper_case (name.[0]) then [name] else []
  | Parser.App(Parser.Const name,args) -> 
     let name = Parser.ASTFuncS.pp name in
     (if upper_case (name.[0]) then [name] else []) @
     (List.fold_left (fun rez arg -> rez @ (get_meta_vars arg)) [] args)
  | Parser.Lam(x,t1) -> get_meta_vars t1
  | _ -> [] in 
 let str_list = List.map (fun (var,pairsl) -> 
  match var with
   | Parser.Const c ->
      let meta_vars = List.fold_left (fun rez f -> 
       rez @ (get_meta_vars f)) [] pairsl in 
      Format.printf "\n%s -> %!" (Parser.ASTFuncS.pp c);
      List.iter (fun var_name -> Format.printf "%s, %!" var_name) meta_vars;
      (Parser.ASTFuncS.pp c) ^ "$\\not\\in\\cup\\{$" ^ 
       (List.fold_left (fun rez var_name -> 
        "FV(" ^ var_name ^ ")," ^ rez) "\\} ; " meta_vars)
   | _ -> "") l in
 List.fold_left (fun rez str -> str ^ rez) "" str_list


let export_clauses cl_list = 
 let headers = 
"\\documentclass[10pt]{article} 

\\usepackage[utf8]{inputenc}
\\usepackage{amssymb}
\\usepackage{color}
\\usepackage{bussproofs}

\\begin{document} \n\n" in
 let rules = List.fold_left (fun l cl ->
(*   let clpair = clausify cl in *)
   let clpair = eta_expand_clause cl in
   let create_pairs = create_context (fst clpair,snd clpair) in
   let fst_ = fst create_pairs in
   let snd_ = snd create_pairs in (*list of fresh vars*)
   let pair_var_metalist = not_in snd_ fst_ in
   let fresh_vars = print_not_in pair_var_metalist in 
   let fresh_str = match snd_ with
     | [] -> ""
     | _ -> "fresh: " in
 (* let label = "\\RightLabel{" ^ fresh_str ^
                 (List.fold_right (fun freshvar l1 ->
                  (export_term freshvar) ^ "," ^ l1) snd_ "" ) ^
                 "}\n" in *)
   let label = "\\RightLabel{" ^ fresh_vars ^ "}\n" in
   let arity = List.length (snd clpair) in
   let rule = match arity with
     | 0 -> "\\AxiomC{$$}\n" ^ "\\UnaryInfC{" ^ (export_term (fst clpair))  ^ "}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 1 -> label ^  "\\UnaryInfC{" ^ (export_pair (None,fst clpair))  ^ "}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 2 -> label ^ "\\BinaryInfC{" ^ (export_pair (None,fst clpair))  ^ "}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 3 -> label ^ "\\TrinaryInfC{" ^ (export_pair (None,fst clpair))  ^ "}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 4 -> label ^ "\\QuaternaryInfC{" ^ (export_pair (None,fst clpair))  ^ "}\n" ^ "\\DisplayProof\\newline\\newline\n\n"
     | 5 -> label ^ "\\QuinaryInfC{" ^ (export_pair (None,fst clpair))  ^ "}\n" ^ "\\DisplayProof\\newline\\newline\n\n" 
     | _ -> Format.printf "\nThe branching factor is > 5!\n%!"; 
            assert false in
   let axioms = List.fold_right (fun cl1 l1 -> "\\AxiomC{" ^ (export_pair cl1) ^ "}\n" ^ l1 ) fst_ "" in
   axioms ^ rule ^ l ) "" cl_list in
 let str = headers ^ rules ^ "\\end{document}" in
 Format.printf "%s%!" str; 
 (*Format.printf "\n\neta: %!";
 let eta = eta_expand_clause (List.nth (List.rev cl_list) 0) in
 print_clause eta; *)
 exit 3;

end
