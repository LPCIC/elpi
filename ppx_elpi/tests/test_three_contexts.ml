let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* Three data types, each one with its own context, whose constructors have
   the same Elpi name (k), told apart by the variant. The context of a predicate
   taking all of them is composed from the three *)

type c1 = E1 of (string[@elpi.key "t1"]) * int
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type t1 =
  | V1 of string [@elpi.var c1]
  | A1 of t1 * t1
  | K1 of int [@elpi.code "k"] [@elpi.variant 1]
  | L1 of int * string *
      (t1[@elpi.binder "t1" c1
         (fun i s -> E1(s,i))])
[@@deriving show, elpi { declaration }]

let t1 :
    'c 'csts.
    (t1, #ctx_for_t1 as 'c, 'csts)
      ContextualConversion.t = t1

type c2 = E2 of (string[@elpi.key "t2"]) * int
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type t2 =
  | V2 of string [@elpi.var c2]
  | A2 of t2 * t2
  | K2 of int [@elpi.code "k"] [@elpi.variant 2]
  | L2 of int * string *
      (t2[@elpi.binder "t2" c2
         (fun i s -> E2(s,i))])
[@@deriving show, elpi { declaration }]

let t2 :
    'c 'csts.
    (t2, #ctx_for_t2 as 'c, 'csts)
      ContextualConversion.t = t2

type c3 = E3 of (string[@elpi.key "t3"]) * int
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type t3 =
  | V3 of string [@elpi.var c3]
  | A3 of t3 * t3
  | K3 of int [@elpi.code "k"] [@elpi.variant 3]
  | L3 of int * string *
      (t3[@elpi.binder "t3" c3
         (fun i s -> E3(s,i))])
[@@deriving show, elpi { declaration }]

let t3 :
    'c 'csts.
    (t3, #ctx_for_t3 as 'c, 'csts)
      ContextualConversion.t = t3

[%%elpi.compose_ctx all [t1; t2; t3]]

open BuiltInPredicate.Notation

let all_to_string = BuiltInPredicate.ContextualPred("all->string",in_ctx_for_all,
  In(t1,"A",
  In(t2,"B",
  In(t3,"C",
  Out(BuiltInData.stringC,"S",
  Read("three data types, each one under its own context"))))),
  fun (a : t1) (b : t2) (c : t3) (_s : string BuiltInPredicate.oarg)
    ~depth:_ ctx (_cst : Data.constraints) (_state : State.t) ->
    let pp_ctx pp = RawData.Constants.Map.pp (PPX.pp_ctx_entry pp) in
    !: (Format.asprintf "@[<hov>%a |- %a@ ;@ %a |- %a@ ;@ %a |- %a@]@\n%!"
      (pp_ctx pp_c1) ctx#c1 t1.pp a
      (pp_ctx pp_c2) ctx#c2 t2.pp b
      (pp_ctx pp_c3) ctx#c3 t3.pp c)
)

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [
    MLCode(all_to_string,DocAbove);
  ])

let program = {|
main :-
  pi x y z\
    e1 x "x" 1 ==> e2 y "y" 2 ==> e3 z "z" 3 ==>
    t1.copy x x ==> t2.copy y y ==> t3.copy z z ==> (
      sigma A B C D E F K1 K2 K3\
        A = (a1 x x),
        B = (l2 2 "w" w\ a2 w y),
        C = (a3 z z),
        print {all->string A B C},
        t1.copy A D, t2.copy B E, t3.copy C F,
        print {all->string D E F},
        % k is the constructor of three types, the type tells which one is meant
        t1.copy (k 1) K1, t2.copy (k 2) K2, t3.copy (k 3) K3,
        K1 = k 1, K2 = k 2, K3 = k 3).
|}

let () = Ppx_tests_lib.run_program builtin program
