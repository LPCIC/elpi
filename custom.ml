(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1                    *)
(* ------------------------------------------------------------------------- *)

open Runtime;;
open Runtime.Utils;;
open Runtime.Pp;;
open Runtime.Constants;;
module F = Parser.ASTFuncS;;

let register_eval, lookup_eval =
 let (evals : ('a, term list -> term) Hashtbl.t)
   =
     Hashtbl.create 17 in
 (fun s -> Hashtbl.add evals (fst (funct_of_ast (F.from_string s)))),
 Hashtbl.find evals
;;

(* Traverses the expression evaluating all custom evaluable functions *)
let rec eval depth =
 function
    Lam _
  | Custom _ -> error "Evaluation of a lambda abstraction or custom predicate"
  | Arg _
  | AppArg _ -> anomaly "Not a heap term"
  | App (hd,arg,args) ->
     let f =
      try lookup_eval hd
      with Not_found -> anomaly (string_of_constant hd ^ " not evaluable") in
     let args = List.map (eval depth) (arg::args) in
     f args
  | UVar ({ contents = g }, from, args) when g != dummy ->
     eval depth (deref ~from ~to_:depth args g)
  | AppUVar ({contents = t}, from, args) when t != dummy ->
     eval depth (app_deref ~from ~to_:depth args t)
  | UVar _
  | AppUVar _ -> error "Evaluation of a non closed term (maybe delay)"
  | Const _
  | String _
  | Int _
  | Float _ as x -> x
;;

let _ =
  register_eval "-" (fun args ->
   match args with
     [ Int x ; Int y ] -> Int (x - y)
   | [ Float x ; Float y ] -> Float (x -. y)
   | _ -> type_error "Wrong arguments to -") ;
  register_eval "+" (fun args ->
   match args with
     [ Int x ; Int y ] -> Int (x + y)
   | [ Float x ; Float y ] -> Float (x +. y)
   | _ -> type_error "Wrong arguments to +") ;
  register_eval "*" (fun args ->
   match args with
     [ Int x ; Int y ] -> Int (x * y)
   | [ Float x ; Float y ] -> Float (x *. y)
   | _ -> type_error "Wrong arguments to *") ;
  register_eval "/" (fun args ->
   match args with
     [ Float x ; Float y ] -> Float (x /. y)
   | _ -> type_error "Wrong arguments to /") ;
  register_eval "mod" (fun args ->
   match args with
     [ Int x ; Int y ] -> Int (x mod y)
   | _ -> type_error "Wrong arguments to mod") ;
  register_eval "div" (fun args ->
   match args with
     [ Int x ; Int y ] -> Int (x / y)
   | _ -> type_error "Wrong arguments to div") ;
  register_eval "^" (fun args ->
   match args with
     [ String x ; String y ] -> String (F.from_string (F.pp x ^ F.pp y))
   | _ -> type_error "Wrong arguments to ^") ;
  register_eval "~" (fun args ->
   match args with
     [ Int x ] -> Int (-x)
   | [ Float x ] -> Float (-. x)
   | _ -> type_error "Wrong arguments to ~") ;
  register_eval "abs" (fun args ->
   match args with
     [ Int x ] -> Int (abs x)
   | [ Float x ] -> Float (abs_float x)
   | _ -> type_error "Wrong arguments to abs") ;
  register_eval "int_to_real" (fun args ->
   match args with
     [ Int x ] -> Float (float_of_int x)
   | _ -> type_error "Wrong arguments to int_to_real") ;
  register_eval "sqrt" (fun args ->
   match args with
     [ Float x ] -> Float (sqrt x)
   | _ -> type_error "Wrong arguments to sqrt") ;
  register_eval "sin" (fun args ->
   match args with
     [ Float x ] -> Float (sin x)
   | _ -> type_error "Wrong arguments to sin") ;
  register_eval "cos" (fun args ->
   match args with
     [ Float x ] -> Float (cos x)
   | _ -> type_error "Wrong arguments to cosin") ;
  register_eval "arctan" (fun args ->
   match args with
     [ Float x ] -> Float (atan x)
   | _ -> type_error "Wrong arguments to arctan") ;
  register_eval "ln" (fun args ->
   match args with
     [ Float x ] -> Float (log x)
   | _ -> type_error "Wrong arguments to ln") ;
  register_eval "floor" (fun args ->
   match args with
     [ Float x ] -> Int (int_of_float (floor x))
   | _ -> type_error "Wrong arguments to floor") ;
  register_eval "ceil" (fun args ->
   match args with
     [ Float x ] -> Int (int_of_float (ceil x))
   | _ -> type_error "Wrong arguments to ceil") ;
  register_eval "truncate" (fun args ->
   match args with
     [ Float x ] -> Int (truncate x)
   | _ -> type_error "Wrong arguments to truncate") ;
  register_eval "size" (fun args ->
   match args with
     [ String x ] -> Int (String.length (F.pp x))
   | _ -> type_error "Wrong arguments to size") ;
  register_eval "chr" (fun args ->
   match args with
     [ Int x ] -> String (F.from_string (String.make 1 (char_of_int x)))
   | _ -> type_error "Wrong arguments to chr") ;
  register_eval "string_to_int" (fun args ->
   match args with
     [ String x ] when String.length (F.pp x) = 1 ->
       Int (int_of_char (F.pp x).[0])
   | _ -> type_error "Wrong arguments to string_to_int") ;
  register_eval "substring" (fun args ->
   match args with
     [ String x ; Int i ; Int j ] when
       i >= 0 && j >= 0 && String.length (F.pp x) >= i+j ->
       String (F.from_string (String.sub (F.pp x) i j))
   | _ -> type_error "Wrong arguments to substring") ;
  register_eval "int_to_string" (fun args ->
   match args with
     [ Int x ] -> String (F.from_string (string_of_int x))
   | _ -> type_error "Wrong arguments to int_to_string") ;
  register_eval "real_to_string" (fun args ->
   match args with
     [ Float x ] -> String (F.from_string (string_of_float x))
   | _ -> type_error "Wrong arguments to real_to_string")
;;


let _ =
  register_custom "$print" (fun ~depth ~env args ->
    Format.printf "@[<hov 1>" ;
    List.iter (Format.printf "%a@ " (uppterm depth [] 0 env)) args ;
    Format.printf "@]\n%!" ;
    []) ;
  register_custom "$lt" (fun ~depth ~env:_ args ->
    let rec get_constant = function
      | Const c -> c
      | UVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (deref ~from:vardepth ~to_:depth args t)
      | AppUVar ({contents=t},vardepth,args) when t != dummy ->
         get_constant (app_deref ~from:vardepth ~to_:depth args t)
      | _ -> error "$lt takes constants as arguments" in
    match args with
    | [t1; t2] ->
        let t1 = get_constant t1 in
        let t2 = get_constant t2 in
        let is_lt = if t1 < 0 && t2 < 0 then t2 < t1 else t1 < t2 in
        if not is_lt then raise No_clause else []
    | _ -> type_error "$lt takes 2 arguments") ;
  List.iter (fun p,psym,pname ->
  register_custom pname (fun ~depth ~env:_ args ->
    match args with
    | [t1; t2] ->
        let t1 = eval depth t1 in
        let t2 = eval depth t2 in
        (match t1,t2 with
           Int _,    Int _
         | Float _,  Float _
         | String _, String _ ->
            if not (p t1 t2) then raise No_clause else []
         | _ ->
           type_error ("Wrong arguments to " ^ psym ^ " (or to " ^ pname^ ")"))
    | _ -> type_error (psym ^ " (or " ^ pname ^ ") takes 2 arguments"))
  ) [(<),"<","$lt_" ; (>),">","$gt_" ; (<=),"=<","$le_" ; (>=),">=","$ge_"] ;
  register_custom "$getenv" (fun ~depth ~env:_ args ->
    match args with
    | [t1; t2] ->
       (match eval depth t1 with
           String s ->
            (try
              let v = Sys.getenv (F.pp s) in
               [ App(eqc, t2, [String (F.from_string v)]) ]
             with Not_found -> raise No_clause)
         | _ -> type_error "bad argument to getenv (or $getenv)")
    | _ -> type_error "getenv (or $getenv) takes 2 arguments") ;
  register_custom "$system" (fun ~depth ~env:_ args ->
    match args with
    | [t1; t2] ->
       (match eval depth t1 with
           String s -> [ App (eqc, t2, [Int (Sys.command (F.pp s))]) ]
         | _ -> type_error "bad argument to system (or $system)")
    | _ -> type_error "system (or $system) takes 2 arguments") ;
  register_custom "$is" (fun ~depth ~env:_ args ->
    match args with
    | [t1; t2] -> [ App (eqc, t1, [eval depth t2]) ]
    | _ -> type_error "is (or $is) takes 2 arguments")
;;
