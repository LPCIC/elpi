open Ast

let rid = ref 0 (* trace_ppx, runtime id *)
let dummy = App("!",[App("!",[])])

let pp_var, pp_reset =
  let l = ref [] in
  (fun v ->
    try
      List.assq v !l
    with Not_found ->
      let s = "X" ^ string_of_int (List.length !l) in
      l := (v,s) :: !l;
      s),
  (fun () -> l := [])

let rec pp fmt = function
  | App(c,[]) -> Format.fprintf fmt "%s" c
  | App(c,l) -> Format.fprintf fmt "@[<hov 2>%s(%a)@]" c (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp) l
  | Var r when !r <> dummy -> pp fmt !r
  | Var r -> let s = pp_var r in Format.fprintf fmt "%s" s
  | Arg i -> Format.fprintf fmt "_%d_" i

let pp_tm = pp
let ppl s = Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f s) pp
let dummy = App("!",[App("!",[])])

let trail = ref []

let assign v t =
  trail := v :: !trail;
  v := t

let rec backtrack o =
  if o != !trail then begin
    match !trail with
    | [] -> assert false
    | v :: vs ->
        v := dummy;
        trail := vs;
        backtrack o
  end

let rec fold_left2 f l1 l2 = match l1, l2 with
  | [], [] -> true
  | x::xs, y::ys -> f x y && fold_left2 f xs ys
  | _ -> false

let rec heapify s = function
  | App(c,l) -> App(c,List.map (heapify s) l)
  | Var _ as x -> x
  | Arg i when s.(i) != dummy -> s.(i)
  | Arg i -> let t = Var (ref dummy) in s.(i) <- t; t

let rec unif (s:tm array) (a:tm) (b:tm) = match a, b with
  (* deref *)
  | Var r, _ when !r != dummy -> unif s !r b
  | _, Var r when !r != dummy -> unif s a !r
  | _, Arg i when s.(i) != dummy -> unif s a s.(i)
  | Arg _, _ -> assert false

  (* assign *)
  | Var r, _ -> assign r (heapify s b); true
  | _, Var r -> assign r a; true (* missing OC *)
  | _, Arg i -> s.(i) <- a; true

  | App(c1,args1), App(c2,args2) ->
    if c1 <> c2 then false
    else fold_left2 (unif s) args1 args2


type goal = tm
[@@deriving show]

type rule = int * tm * tm list
[@@deriving show]

type frame =
  | Done
  | Todo of {
      brothers : goal list;
      cutinfo : alt list; [@printer (fun _ _ -> ())]
      siblings : frame;
    }
and alt = {
  goal: goal;
  rules : rule list; [@printer (fun _ _ -> ())]
  stack : frame; [@printer (fun _ _ -> ())]
  old_trail : tm ref list; [@printer (fun _ _ -> ())]
  cutinfo : alt list; [@printer (fun _ _ -> ())]

}
[@@deriving show]
type alts = alt list
[@@deriving show]

let all_rules = ref []
let gas = ref 0

let rec run goal rules next (alts : alts) (cutinfo : alts) =
  [%trace "run" ~rid 
    ("@[<hov 2>g: %a@ next: %a@ alts: %a@]@\n" pp_tm goal pp_frame next pp_alts alts)
  begin 
  if !gas = 0 then `TIMEOUT else begin decr gas;
  (* CONTROL *)
  if goal = App("!",[]) then pop_andl next cutinfo
  (* TABLE *)
  (* SLD *)
  else match rules with
  | [] -> next_alt alts
  | (stack,hd,conds)::rules ->
      [%spy "select" ~rid (fun fmt () -> Format.fprintf fmt "%a :- %a." pp_tm hd pp_tm (App("&",conds))) ()];
      let old_trail = !trail in
      let stack = Array.init stack (fun _ -> dummy) in
      if not (unif stack goal hd) then begin
        backtrack old_trail;
        run goal rules next alts cutinfo
      end else
        let old_alts = alts in
        let alts =
          if rules = [] then alts
          else { goal; rules; stack=next; old_trail; cutinfo } :: alts in
        match List.map (heapify stack) conds with
        | [] -> pop_andl next alts
        | goal :: rest ->
           let next = Todo { brothers = rest; cutinfo; siblings = next } in
           run goal !all_rules next alts old_alts
end end]
and pop_andl next alts =
  match next with
  | Done -> `OK alts
  | Todo { brothers = []; siblings = next; _ } -> pop_andl next alts
  | Todo { brothers = goal :: brothers; cutinfo; siblings } ->
      run goal !all_rules (Todo { brothers = brothers; cutinfo; siblings }) alts cutinfo
            
and next_alt = function
  | [] -> `FAIL
  | { goal; rules; stack=next; old_trail; cutinfo } :: alts ->
      backtrack old_trail;
      run goal rules next alts cutinfo

let run goal rules =
  match goal with
  | [] -> assert false
  | [g] -> run g rules Done [] []
  | g::gs -> run g rules (Todo { brothers = gs; siblings = Done; cutinfo = []}) [] []

let const x = App(x,[])

module P = struct

  let l = ref []
  let rec vars = function
    | App(s,[]) ->
        begin match s.[0] with
        | 'A'..'Z' -> 
            begin try
              let i = List.assoc s !l in
              Arg i
            with Not_found ->
              l := (s, List.length !l) :: !l;
              Arg (List.assoc s !l)
            end
        | _ -> App(s,[])
        end
    | App(x,xs) -> App(x,List.map vars xs)
    | x -> x
  

  let parse_program s = try
    let lexbuf = Lexing.from_string s in
    let cl = Parser.program Lexer.token lexbuf in
    cl |> List.map (fun (hd,hyps) ->
        l := [];
        let hd = vars hd in
        let hyps = List.map vars hyps in
        List.length !l, hd, hyps)
    with Parser.Error -> Format.eprintf "cannot parse %s\n%!" s; exit 1

  let parse_query s = try
    l := [];
    let lexbuf = Lexing.from_string s in
    let goals = Parser.query Lexer.token lexbuf in
    let goals = List.map vars goals in
    let stack = Array.init (List.length !l) (fun _ -> dummy) in
    let goals = List.map (heapify stack) goals in
    goals
  with Parser.Error -> Format.eprintf "cannot parse %s\n%!" s; exit 1

end

let main query steps n program =
  let program = P.parse_program program in
  let query = P.parse_query query in
  all_rules := program;
  gas := steps;
  pp_reset ();
  let rec all n = function
  | `FAIL -> [Format.asprintf "no"]
  | `TIMEOUT -> [Format.asprintf "steps"]
  | `OK alts ->
      let s = Format.asprintf "%a" (ppl ", ") query in
      if n = 1 then [s]
      else s :: all (n-1) (next_alt alts)
  in
  all n (run query !all_rules)

let check ?(steps=100) s p q n l1 =
  let l2 = main q steps n p in
  if l1 <> l2 then
    Format.eprintf "ERROR: %s:\n%a\n%a\n%!" s
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l1
      (Format.pp_print_list ~pp_sep:(fun f () -> Format.pp_print_string f " ") Format.pp_print_string) l2
  else
    Format.eprintf "%s: ok\n%!" s

let () =
  let _ = Trace_ppx_runtime.Runtime.parse_argv (Array.to_list Sys.argv) in

  check "transitive closure fwd nofail"
      "
      t(a,b).
      t(a,c).
      t(b,d).
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      "
    "t(a,X)" 4 ["t(a, b)"; "t(a, c)"; "t(a, d)"; "steps"];

  check "transitive closure fwd fail after solutions"
      "
      t(a,b).
      t(a,c).
      t(b,d).
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      "
    "t(a,X)" 4 ["t(a, b)"; "t(a, c)"; "t(a, d)"; "steps"];

  check "transitive closure loop"
      "
      t(X,Y) :- t(X,Z), t(Z,Y).
      t(X,X).
      t(a,b).
      t(a,c).
      t(b,d).
      "
    "t(a,X)" 1 ["steps"];

  check "cut fail"
      "
      t :- !, fail.
      t.
      "
    "t" 1 ["no"];

  check "cut"
      "
      t.
      t :- !, fail.
      "
    "t" 2 ["t"; "no"];

  check "tail cut"
      "
      t.
      t.
      p :- t, !.
      "
    "p" 2 ["p"; "no"];

  check "tail no cut"
      "
      t.
      t.
      p :- t.
      "
    "p" 3 ["p"; "p"; "no"];

;;


