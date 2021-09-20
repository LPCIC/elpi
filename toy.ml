let rid = ref 0 (* trace_ppx, runtime id *)

type tm =
  | App of char * tm list
  | Var of tm ref
  | Arg of int

let dummy = App('!',[App('!',[])])

let pp_var =
  let l = ref [] in
  fun v ->
    try
      List.assq v !l
    with Not_found ->
      let s = "X" ^ string_of_int (List.length !l) in
      l := (v,s) :: !l;
      s

let rec pp fmt = function
  | App(c,[]) -> Format.fprintf fmt "%c" c
  | App(c,l) -> Format.fprintf fmt "@[<hov 2>%c(%a)@]" c (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.fprintf fmt ",@ ") pp) l
  | Var r when !r != dummy -> pp fmt !r
  | Var r -> let s = pp_var r in Format.fprintf fmt "%s" s
  | Arg i -> Format.fprintf fmt "_%d_" i

let pp_tm = pp

let dummy = App('!',[App('!',[])])

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
    if c1 != c2 then false
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
}
[@@deriving show]
type alts = alt list
[@@deriving show]

let all_rules = ref []
let gas = ref 0

let rec run goal rules next (alts : alts) =
  [%trace "run" ~rid 
    ("@[<hov 2>g: %a@ next: %a@ alts: %a@]@\n" pp_tm goal pp_frame next pp_alts alts)
  begin 
  if !gas = 0 then `TIMEOUT else begin decr gas;
  match rules with
  | [] -> next_alt alts
  | (stack,hd,conds)::rules ->
      [%spy "select" ~rid (fun fmt () -> Format.fprintf fmt "%a :- %a." pp_tm hd pp_tm (App('&',conds))) ()];
      let old_trail = !trail in
      let stack = Array.init stack (fun _ -> dummy) in
      if not (unif stack goal hd) then begin
        backtrack old_trail;
        run goal rules next alts
      end else
        let alts =
          if rules = [] then alts
          else { goal; rules; stack=next; old_trail } :: alts in
        match List.map (heapify stack) conds with
        | [] -> pop_andl next alts
        | goal :: rest ->
           let next = Todo { brothers = rest; cutinfo = alts; siblings = next } in
           run goal !all_rules next alts
end end]
and pop_andl next alts =
  match next with
  | Done -> `OK alts
  | Todo { brothers = []; siblings = next; _ } -> pop_andl next alts
  | Todo { brothers = goal :: brothers; cutinfo; siblings } ->
      run goal !all_rules (Todo { brothers = brothers; cutinfo; siblings }) alts
            
and next_alt = function
  | [] -> `FAIL
  | { goal; rules; stack=next; old_trail } :: alts ->
      backtrack old_trail;
      run goal rules next alts

let const x = App(x,[])

let tr_closure = [
    (3, App('t',[Arg 0; Arg 1]), [ App('t',[Arg 0;Arg 2]) ; App('t',[Arg 2;Arg 1])  ]);
    (1, App('t',[Arg 0; Arg 0]), []);
]

let graph1 = [
    (0, App('t',[const 'a'; const 'b']), []);
    (0, App('t',[const 'a'; const 'c']), []);
    (0, App('t',[const 'b'; const 'd']), []);
]

let main program query steps n =
  all_rules := program;
  gas := steps;
  Format.eprintf "@\n%!query: %a@\n%!" pp query;
  let rec all n = function
  | `FAIL -> Format.eprintf "no more solutions@\n%!"
  | `TIMEOUT -> Format.eprintf "no more steps@\n%!"
  | `OK alts ->
      Format.eprintf "solution %d: %a@\n%!" n pp query;
      if n = 1 then Format.eprintf "stop@\n%!"
      else all (n-1) (next_alt alts)
  in
  all n (run query !all_rules Done [])

let () =
  let _ = Trace_ppx_runtime.Runtime.parse_argv (Array.to_list Sys.argv) in

  main (graph1 @ tr_closure) (App('t',[const 'a';Var(ref dummy)])) 100 3;
  main (tr_closure @ graph1) (App('t',[const 'a';Var(ref dummy)])) 100 3;

