(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)


(* ------ LaTeX exporter ------- *)

(* if  q :- a,b,c  returns a pair (q,[a;b;c]) *)
let clausify t = match t with
  | Elpi_ast.App(Elpi_ast.Const f,tl) ->
     (match tl with
        | [left;right] when Elpi_ast.Func.show f = (Elpi_ast.Func.show Elpi_ast.Func.rimplf) ->
            let rec hyps andl = (match andl with
              | Elpi_ast.App(Elpi_ast.Const f,conjl) when Elpi_ast.Func.show f = (Elpi_ast.Func.show Elpi_ast.Func.andf) -> (match conjl with
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
    | Elpi_ast.Const(v1) when v = v1 -> Elpi_ast.Const newv
    | Elpi_ast.Custom(v1) when v = v1 -> Elpi_ast.Custom newv
    | Elpi_ast.App(t1,tl) ->
       let newtl = List.map (fun x -> subst x v newv) tl in
       Elpi_ast.App(t1,newtl)
    | Elpi_ast.Lam(v1,tm) when v = v1 -> Elpi_ast.Lam(newv,subst tm v newv)
    | Elpi_ast.Lam(v1,tm) -> Elpi_ast.Lam(v1,subst tm v newv)
    | _ -> t in
  match lambda with
    | Elpi_ast.Lam(v,_) -> 
        incr cnt; subst lambda v (Elpi_ast.Func.from_string ("x_{" ^ (string_of_int !cnt) ^ "}"))
    | _ -> lambda





(* (q,[a; b=>c; d; pi x\ (f x)] returns 
     ([(None,a);(b,c);(None,d);(None,f x)], [x])*)
let create_context pairsl =
  let fresh_vars = ref [] in 
  let rec aux = function
  | [] -> []
  | (Elpi_ast.App(Elpi_ast.Const f,tl) as fla)::rest -> (match tl with
      | [left;right] when Elpi_ast.Func.show f = (Elpi_ast.Func.show Elpi_ast.Func.implf) -> (Some left,right) :: (aux rest)
      | [Elpi_ast.Lam(_,_) as lam] when Elpi_ast.Func.show f = (Elpi_ast.Func.show Elpi_ast.Func.pif) ->
          let newlam = rename_bound_var lam in
          (match newlam with
            | Elpi_ast.Lam(v,t) -> 
                fresh_vars := !fresh_vars @ [Elpi_ast.Const v]; 
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
 | Elpi_ast.Const f
 | Elpi_ast.Custom f ->
    (match v with 
     | Elpi_ast.Const sym -> Elpi_ast.Func.show f = Elpi_ast.Func.show sym 
     | _ -> assert false (* v should be a term: Const of Func.t *))
 | Elpi_ast.App (Elpi_ast.Const hd,xs) -> 
    List.fold_left (fun rez x -> rez || (contains_var x v)) false xs 
 | Elpi_ast.Lam (_,t1) -> contains_var t1 v
 | _ -> false    

    
(* exports a f-la occurrence, i.e. q,a,b,c f-las from above *)
let export_term tm = 
  let rec aux prec t = match t with
    Elpi_ast.Const f 
  | Elpi_ast.Custom f -> 
     let name = Elpi_ast.Func.show f in 
     (try "<<>>" ^ (Elpi_parser.get_literal name) ^ "<<>>" with Not_found ->
      "\\:" ^ name ^ "\\:")
        (* pp_app f ppconstant (aux max_int depth) (hd,xs) *)
  | Elpi_ast.App (Elpi_ast.Const hd,x::xs)
  | Elpi_ast.App (Elpi_ast.Custom hd,x::xs) ->
    (try
     let assoc,hdlvl = Elpi_parser.precedence_of hd in
     let lbracket,rbracket= if hdlvl < prec then ("\\:(",")\\:") else ("","") in
      lbracket ^
       (match assoc with
        | Elpi_parser.Infix when List.length xs = 1 ->
          (aux (hdlvl+1) x) ^ " " ^
          (aux 1000 (Elpi_ast.Const hd)) ^ " " ^
          (aux (hdlvl+1) (List.hd xs))
        | Elpi_parser.Infixl when List.length xs = 1 ->
          (aux hdlvl x) ^ " " ^
          (aux 1000 (Elpi_ast.Const hd)) ^ " " ^
          (aux (hdlvl+1)) (List.hd xs)
        | Elpi_parser.Infixr when List.length xs = 1 ->
          (aux (hdlvl+1) x) ^ " " ^
          (aux 1000 (Elpi_ast.Const hd)) ^ " " ^ 
          (aux hdlvl) (List.hd xs)
        | Elpi_parser.Prefix when xs = [] ->
          (aux 1000 (Elpi_ast.Const hd)) ^ " " ^
          (aux hdlvl x)
        | Elpi_parser.Postfix when xs = [] ->
          (aux hdlvl x) ^ " " ^
          (aux 1000 (Elpi_ast.Const hd)) 
        | _ -> (aux 1001 (Elpi_ast.Const hd)) ^ " " ^
               (List.fold_left (fun l x -> l^(aux 1000 x)^(if (!cnt = 1) then "" else (decr cnt;" "))) "" (x::xs)) ) ^ rbracket
     with Not_found -> 
      let hdlvl = max_int - 1 in
      let lbracket,rbracket= if hdlvl < prec then ("\\:(",")\\:") else ("","") in
      let cnt = ref (List.length (x::xs)) in
      lbracket ^ (aux max_int (Elpi_ast.Const hd)) ^ " " ^
      (List.fold_left (fun l x -> l^(aux max_int x)^(if (!cnt = 1) then "" else (decr cnt;" "))) "" (x::xs)) ^ rbracket) 

(*
 | Elpi_ast.App(f,tl) -> 
    (match tl with
    | [] -> export_term prec f
    | [x] -> 
       if (export_term prec f) == (Elpi_ast.Func.show Elpi_ast.Func.pif) then
        match x with
          Elpi_ast.Lam(_,_) ->  "(" ^ " \\forall " ^ (export_term x) ^ ")"
        | _ -> assert false 
       else
        (export_term f) ^ "(" ^ (export_term x) ^ ")"
    | [x;y] -> 
       if (export_term f) == (Elpi_ast.Func.show Elpi_ast.Func.eqf) then
        "(" ^ (export_term x) ^ " = " ^ (export_term y) ^ ")"
       else if (export_term f) == (Elpi_ast.Func.show Elpi_ast.Func.implf) then
        "(" ^  (export_term x) ^ " \\rightarrow " ^ (export_term y) ^ ")" 
       else if (export_term f) == (Elpi_ast.Func.show Elpi_ast.Func.andf) then
         "(" ^ (export_term x) ^ " \\wedge " ^ (export_term y) ^ ")"
       else if (export_term f) == (Elpi_ast.Func.show Elpi_ast.Func.orf) then
         "(" ^ (export_term x) ^ " \\vee " ^ (export_term y) ^ ")"
       else (export_term f) ^ "(" ^ (export_term x) ^ "," ^ (export_term y) ^ ")"
    | _ -> let last,tail = (List.hd (List.rev tl)), (List.rev (List.tl (List.rev tl))) in
      (export_term f) ^ "(" ^ (List.fold_left (fun l x -> l^(export_term x)^",") "" tail) ^ (export_term last) ^ ")" )  *)
  | Elpi_ast.Lam (x,t1) ->
     " lambda"^ Elpi_ast.Func.show x^"." ^ (aux prec t1)
  | Elpi_ast.String str -> "\\:" ^ Elpi_ast.Func.show str ^ "\\:"
  | Elpi_ast.Int i -> "\\:" ^ (string_of_int i) ^ "\\:" 
  | Elpi_ast.Float i -> "\\:" ^ (string_of_float i) ^ "\\:" 
  | _ -> assert false in
(* let pats =
  [ Str.regexp "\$", "\\$" (* for the custom predicates which start with $*)
  ; Str.regexp "<<>>",  "$" (* for mathematical mode in LaTeX, it is hidden from the user *)
  ; Str.regexp "_",  "\\_" (*for the _,otherwise exports it as a subscript*)
  ; Str.regexp "lambda", "$\\lambda$" ] in
 let new_tm = aux 0 tm in
 List.fold_left (fun s (a,b) -> Str.global_replace a b s) new_tm pats;;
*) aux 1 tm;;


(* exports b => c, i.e. (b,c) to b |- c*)
let export_pair = function
  | (None,b) -> "\\Gamma\\vdash " ^ export_term b
  | (Some a,b) -> " \\Gamma," ^ export_term a ^" \\vdash "^  export_term b


(*hd :- a,b,c  is the cl_pair (hd,[a,b,c])*)
let print_clause cl_pair =
 let rec print_fla f = match f with
  | Elpi_ast.Const c
  | Elpi_ast.Custom c -> Format.printf "%s%!" (Elpi_ast.Func.show c)
  | Elpi_ast.App(Elpi_ast.Const hd,tl)
  | Elpi_ast.App(Elpi_ast.Custom hd,tl) ->
     Format.printf "(%s %!" (Elpi_ast.Func.show hd);
     List.iter (fun x -> print_fla x; Format.printf " %!") tl;
     Format.printf ")%!";
  | Elpi_ast.Lam(x,t) ->
     Format.printf "λ%!";
     print_fla (Elpi_ast.Const x);
     Format.printf ".%!";
     print_fla t
  | _ -> Format.printf "not_important%!"; in
 print_fla (fst cl_pair);
 Format.printf " :- %!";
 List.iter (fun x -> (print_fla x); Format.printf ", %!";) (snd cl_pair);;


(* a pair (main_pred,[a;b;$name_one]) is rewritten to the pair
   (main\_pred,[a;b;\$name\_one]) *)
let export_identifiers pair =
 let replace name =
  let paths =
   [ Str.regexp "\\$", "\\$" (* for the custom predicates which start with $*)
   ; Str.regexp "<<>>",  "$" (* for mathematical mode in LaTeX, it is hidden from the user *)
   ; Str.regexp "_",  "\\_" (*for the _,otherwise exports it as a subscript*)
   ; Str.regexp "lambda", "$\\lambda$" ] in
  List.fold_left (fun s (a,b) -> Str.global_replace a b s) name paths in
 let rec aux t = match t with
  | Elpi_ast.Const c ->
     let name = Elpi_ast.Func.show c in
     Elpi_ast.Const(Elpi_ast.Func.from_string (replace name))
  | Elpi_ast.Custom c ->
     let name = Elpi_ast.Func.show c in
     Elpi_ast.Custom(Elpi_ast.Func.from_string (replace name))
  | Elpi_ast.App(f,args) ->
     Elpi_ast.App(aux f, List.map (fun x -> aux x) args)
  | Elpi_ast.Lam(x,arg) -> Elpi_ast.Lam(x, aux arg)
  | _ -> t in
 let hd = aux (fst pair) in
 let tl = List.map (fun x -> aux x) (snd pair) in
 (hd,tl);;
 


(* g F :- F a b  gives a eta-expanded clause, 
   i.e. the pair (f (\x\y. F) , F a b) *)
let eta_expand_clause cl = 
 let module FunctMap = Map.Make(Elpi_ast.Func) in
 let arity_map = ref FunctMap.empty in
 (* adds the arity of a functor in the arity_map *) 
 let rec get_arity f = match f with
  | Elpi_ast.App(Elpi_ast.Const c, args) ->
     arity_map := FunctMap.add c (List.length args) !arity_map;
     List.iter (fun x -> get_arity x) args
  | Elpi_ast.App(Elpi_ast.Custom c, args) ->
     arity_map := FunctMap.add c (List.length args) !arity_map;
     List.iter (fun x -> get_arity x) args;
  | Elpi_ast.Lam(c,t) -> get_arity t
  | _ -> () in
 (* eta-exand f to its arity*)
 let rec add_lambdas f = match f with
  | Elpi_ast.Const c as name-> 
     (try let n = FunctMap.find c !arity_map in
     let rec aux i = (match i with
      | 0 -> [] 
      | _ -> 
        let var = Elpi_ast.Func.from_string ("v" ^ (string_of_int i)) in
        var :: (aux (i-1))) in
     let varl = aux n in
     List.fold_left (fun rez x -> Elpi_ast.Lam(x,rez)) name varl
     with Not_found -> f) 
  | Elpi_ast.Lam(x,t) -> Elpi_ast.Lam(x,add_lambdas t) 
  | Elpi_ast.App(name,tl) -> 
     let tl = List.map (fun x -> add_lambdas x) tl in
     let newf = Elpi_ast.App(name, tl) in
     newf
  | _ -> f in
 let cl = clausify cl in
 let cl = export_identifiers cl in
 List.iter (fun x -> get_arity x) ((fst cl)::(snd cl));
 let head = add_lambdas (fst cl) in
 let tail = List.map (fun f -> add_lambdas f) (snd cl) in
 (head,tail) 

(*from the pair ([(None,a);(b,H a);(None,F x)], [x,y]) where 
  [x,y] are the fresh vars, returns: 
   (Elpi_ast.term * (term list)) list
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
let print_label l =
 let upper_case c = c >= 'A' && c <= 'Z' in
(* returns the meta-variables in term t *)
 let rec get_meta_vars t = match t with
  | Elpi_ast.Const c | Elpi_ast.Custom c -> 
   let name = Elpi_ast.Func.show c in
   if upper_case (name.[0]) then [name] else []
  | Elpi_ast.App(Elpi_ast.Const name,args) -> 
     let name = Elpi_ast.Func.show name in
     (if upper_case (name.[0]) then [name] else []) @
     (List.fold_left (fun rez arg -> rez @ (get_meta_vars arg)) [] args)
  | Elpi_ast.Lam(x,t1) -> get_meta_vars t1
  | _ -> [] in 
 let str_list = List.map (fun (var,pairsl) -> 
  match var with
   | Elpi_ast.Const c ->
      let meta_vars = List.fold_left (fun rez f -> 
       rez @ (get_meta_vars f)) [] pairsl in 
      let len = ref (List.length meta_vars) in
      "$" ^ (Elpi_ast.Func.show c) ^ " \\not\\in\\bigcup \\{" ^ 
       (List.fold_right (fun var_name rez ->
        decr len; 
        (if (!len)>0 then "{,}" else "") ^ "FV(" ^ var_name ^ ")" ^ rez) meta_vars "\\} $ \\\\ ")
   | _ -> "") l in
 List.fold_left (fun rez str -> str ^ rez) "" str_list

(*
let export_clauses_bussproofs cl_list = 
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
   let label = if fresh_vars = "" then "" else
     "\\RightLabel{\\tiny \\begin{tabular}{l}" ^ fresh_vars ^ "\end{tabular} }\n" in 
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
 (*Format.printf "%s%!" str;*) 
 (*Format.printf "\n\neta: %!";
 let eta = eta_expand_clause (List.nth (List.rev cl_list) 0) in
 print_clause eta; *)
 str;;
*)


let header = "\\documentclass[10pt]{article} 

\\usepackage[utf8]{inputenc}
\\usepackage{amssymb}
\\usepackage{color}
\\usepackage{mathpartir}

\\begin{document} \n\n"

let open_tex_file = ref stdout;;
let flag = ref false;;

let activate () = flag := true;;

let export_clause cl =
 if not !flag then ()
 else begin
  let clpair = eta_expand_clause cl in
  let create_pairs = create_context (fst clpair,snd clpair) in
  let fst_ = fst create_pairs in
  let snd_ = snd create_pairs in (*list of fresh vars*)
  let pair_var_metalist = not_in snd_ fst_ in
  let fresh_vars = print_label pair_var_metalist in
  let label = if fresh_vars = "" then "" else
   "\\tiny\n\\begin{tabular}{l}\n" ^ fresh_vars ^ "\n\\end{tabular} \n" in
  let consequence = export_pair (None,fst clpair) in
  let axioms = List.fold_right (fun cl1 l1 -> (export_pair cl1) ^ " \\\\ " ^ l1 ) fst_ "" in
  let axioms = if axioms = "" then "~" else axioms in
  let rule = "${\\inferrule* [right =$\n" ^ label ^ "$]\n" ^ "{" ^ axioms ^ "}\n" ^ "{" ^ consequence ^ "}" ^ "\n}$\\\\\\\\\\\\ \n" in
  Printf.fprintf !open_tex_file "%s\n%!" rule
 end
;;

let process ~path:filename ~shortpath f inp =
 if !flag then begin
  let old_open_tex_file = !open_tex_file in
  let filename_without_extension = Filename.chop_extension filename in
  let filename_tex = filename_without_extension ^ ".tex" in
  let ch_out_tex = open_out filename_tex in
  Format.printf "LaTeX exporting %s\n%!" shortpath;
  let procent_str = (String.make 1 '%') in
  Printf.fprintf ch_out_tex "%s\n%s\n\n%!" (procent_str ^" This file is automatically generated from the file:") (procent_str ^ " " ^ shortpath);
  Printf.fprintf ch_out_tex "%s%!" header;
  open_tex_file := ch_out_tex ;
  let res = f inp in
  Printf.fprintf ch_out_tex "\n\n\\end{document}%!";
  close_out ch_out_tex;
  open_tex_file := old_open_tex_file ;
  res
 end else f inp
;;

Elpi_parser.PointerFunc.set_latex_export
 { Elpi_parser.PointerFunc.process = process ; export = export_clause };;
