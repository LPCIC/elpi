(* GC off
let _ =
  let control = Gc.get () in
  let tweaked_control = { control with
    Gc.space_overhead = max_int;
  } in
  Gc.set tweaked_control
;;
*)

(* Invariant: a Heap term never points to a Query term *)
type term =
  (* Pure terms *)
  | Const of string
  (* Query terms *)
  | Struct of term list
  | Arg of int
  (* Heap terms *)
  | App of term list
  | UVar of term ref

let dummy = App []

let ppterm f t =
  let rec ppapp a c1 c2 = 
    Format.fprintf f "%c@[<hov 1>" c1;
    List.iter (fun x -> aux x; Format.fprintf f "@ ") a;
    Format.fprintf f "@]%c" c2
  and aux = function
    | App a -> ppapp a '(' ')'
    | Struct a -> ppapp a '{' '}'
    | UVar { contents = t } -> aux t
    | Const s -> Format.fprintf f "%s" s
    | Arg i -> Format.fprintf f "A%d" i
  in
    aux t
;;

type key = string * string

type clause = { hd : term; hyps : term list; vars : int; key : key }

let dummyk = "dummy"

let key_of = function
  | (App xs | Struct xs) -> begin
      match xs with
      | Const w :: (App ys | Struct ys) :: _ -> begin
          match ys with
          | Const z :: _ -> w,z
          | _ -> w, dummyk
          end
      | Const w :: Const z :: _ -> w,z
      | Const w :: _ -> w,dummyk
      | _ -> dummyk, dummyk
  end
  | _ -> dummyk, dummyk

let clause_match_key (j1,j2) { key = (k1,k2) } =
  j1 == dummyk || k1 == dummyk ||
  (j1 == k1 && (j2 == dummyk || k2 == dummyk || j2 == k2))

(* The environment of a clause and stack frame *)

let mk_env size = Array.create size dummy

let to_heap e t =
  let rec aux = function
    | (Const _ | UVar _ | App _) as x -> x (* heap term *)
    | Struct b -> App (List.map aux b)
    | Arg i ->
        let a = e.(i) in
        if a == dummy then
            let v = UVar(ref dummy) in
            e.(i) <- v;
            v
        else aux a
  in aux t
;;

type frame = {
  env : term array;
  lvl : int;
  goals : (key * term) list;
  next : frame;
}

let mk_frame stack_top (c : clause) = {
  env = mk_env c.vars;
  lvl = 1 + stack_top.lvl;
  goals = List.map (fun x -> (dummyk,dummyk), x) c.hyps;
  next = stack_top;
}

(* Unification *)

let trail_this (trail,no_alternative) old =
  match no_alternative with
  | true -> ()
  | false -> trail := old :: !trail

(* Invariant: LSH is a heap term *)
let unif trail e_a e_b a b =
 let rec unif a b =
   (* Format.eprintf "unif: %a = %a\n%!" ppterm a ppterm b; *)
   a == b || match a,b with
   | (Arg _ | Struct _), _ -> assert false
   | _, Arg i when e_b.(i) != dummy -> unif a e_b.(i)
   | UVar { contents = t }, _ when t != dummy -> unif t b
   | _, UVar { contents = t } when t != dummy -> unif a t
   | UVar _, Arg j -> e_b.(j) <- a; true
   | t, Arg i -> trail_this trail (`Arr (e_b,i)); e_b.(i) <- t; true
   | UVar r, t -> trail_this trail (`Ref r); r := to_heap e_b t; true
   | t, UVar r -> trail_this trail (`Ref r); r := t; true
   | Const x, Const y -> x == y (* !!! hashcons the entire Const node *)
   | App xs, (Struct ys | App ys) -> List.for_all2 unif xs ys
   | Const _, (App _ | Struct _) -> false
   | App _, Const _  -> false in
 unif a b
;;

(* Backtracking *)

type trail = [ `Arr of term array * int | `Ref of term ref ]

type alternative = {
  stack : frame;
  trail : trail list;
  clauses : clause list
}

let undo_trail old_trail trail =
  while !trail != old_trail do
    match !trail with
    | `Ref r :: rest -> r := dummy; trail := rest
    | `Arr(a,i) :: rest -> a.(i) <- dummy; trail := rest
    | _ -> assert false
  done
;;

(* Loop *)

let put_all_args f = { f with
   goals = List.map (fun (_,x) ->
     let x = to_heap f.env x in
     key_of x, x)
   f.goals
}

let run1 trail e_g g c stack last_call =
  let old_trail = !trail in
  let f = mk_frame stack c in
  if unif (trail,last_call) e_g f.env g c.hd
  then Some (put_all_args f)
  else (undo_trail old_trail trail; None)
;;

let rec select trail e_g g stack p old_stack alts =
  match p with
  | [] -> None
  | c :: cs ->
     let old_trail = !trail in
     match run1 trail e_g g c stack (alts = []) with
     | None -> select trail e_g g stack cs old_stack alts
     | Some new_stack ->
         Some (new_stack, (* crucial *)
               if cs = [] then alts
               else { stack = old_stack; trail = old_trail; clauses = cs }
                    :: alts)
;;

let filter cl k = List.filter (clause_match_key k) cl

let set_goals s gs = { s with goals = gs }

let rec run p cp trail (stack : frame) alts =
  match stack.goals with
  | [] ->
      if stack.lvl == 0 then () else run p p trail stack.next alts
  | (key_g,g) :: gs ->
      let cp = filter cp key_g in
      match select trail stack.env g (set_goals stack gs) cp stack alts with
      | Some (stack, alts) -> run p p trail stack alts
      | None ->
          match alts with
          | [] -> raise (Failure "no clause")
          | { stack; trail = old_trail; clauses } :: alts ->
              undo_trail old_trail trail;
              run p clauses trail stack alts
;;
let run p s = run p p (ref []) s []
  

(* Test *)

(* Hashconsed constants *)
let appk = "app"
let nilk = "nil"
let revk = "rev"
let eqk = "eq"
let consk = "cons"
let ak = "a"
let bk = "b"

let cak = Const ak
let cbk = Const bk
let cconsk = Const consk
let cnilk = Const nilk
let cappk = Const appk
let crevk = Const revk

(* Program *)
let app1 = { hd = Struct[ cappk; cnilk; Arg 0; Arg 0 ]; hyps = []; vars = 1; key = (appk,nilk) };;
let app2 = { hd = Struct[ cappk; Struct[cconsk; Arg 0; Arg 1]; Arg 2; Struct [cconsk; Arg 0; Arg 3 ] ]; hyps = [ Struct [ cappk; Arg 1; Arg 2; Arg 3] ]; vars = 4; key = (appk,consk) };;

let rev1 = { hd = Struct[ crevk; cnilk; Arg 0; Arg 0 ]; hyps = []; vars = 1; key = (revk,nilk) };;
let rev2 = { hd = Struct[ crevk; Struct[ cconsk; Arg 0; Arg 1]; Arg 2; Arg 3 ];
             hyps = [Struct[crevk; Arg 1; Struct [ cconsk; Arg 0; Arg 2]; Arg 3]];
             vars = 4; key = (revk,consk) };;
let refl = { hd = Struct[ Const eqk; Arg 0; Arg 0]; hyps = []; vars = 1; key = (eqk,dummyk) };;

let l1 =
   App [ cconsk; cak; App [ cconsk; cbk; 
   App [ cconsk; cak; App [ cconsk; cbk; 
   App [ cconsk; cak; App [ cconsk; cbk; 
   App [ cconsk; cak; App [ cconsk; cbk; 
   App [ cconsk; cak; App [ cconsk; cbk; 
   cnilk ]]]]]]]]]];;
let gs =
  let v1 = UVar (ref dummy) in
  let v2 = UVar (ref dummy) in
  let v3 = UVar (ref dummy) in
  let v4 = UVar (ref dummy) in
  let v5 = UVar (ref dummy) in
  let v6 = UVar (ref dummy) in
  let v7 = UVar (ref dummy) in
  let v8 = UVar (ref dummy) in
  let v9 = UVar (ref dummy) in
  let v10 = UVar (ref dummy) in
  let v11 = UVar (ref dummy) in
  let v12 = UVar (ref dummy) in
  let v13 = UVar (ref dummy) in
  let v14 = UVar (ref dummy) in
  let r1 = UVar (ref dummy) in
  let r2 = UVar (ref dummy) in
  let a1 = [cappk; l1; l1; v1] in
  let a2 = [cappk; v1; v1; v2] in
  let a3 = [cappk; v2; v2; v3] in
  let a4 = [cappk; v3; v3; v4] in
  let a5 = [cappk; v4; v4; v5] in
  let a6 = [cappk; v5; v5; v6] in
  let a7 = [cappk; v6; v6; v7] in
  let a8 = [cappk; v7; v7; v8] in
  let a9 = [cappk; v8; v8; v9] in
  let a10 = [cappk; v9; v9; v10] in
  let a11 = [cappk; v10; v10; v11] in
  let a12 = [cappk; v11; v11; v12] in
  let a13 = [cappk; v12; v12; v13] in
  let a14 = [cappk; v13; v13; v14] in
  let aR1 = [crevk; v14; cnilk; r1] in
  let aR2 = [crevk; r1; cnilk; r2] in
  [
          App a1;
          App a2;
          App a3;
          App a4;
          App a5;
          App a6;
          App a7;
          App a8;
          App a9;
          App a10;
          App a11;
          App a12;
          App a13;
          App a14;
          App aR1;
          App aR2;
          App [Const eqk; v14;r2] 
  ];;

let p = [app1;app2;rev1;rev2;refl];;
let rec top = { lvl = 0; env = mk_env 0; goals = List.map (fun x -> key_of x, x) gs; next = top; };;
run p top;;
