let file_name = Sys.argv.(1)

open Elpi.API

let declaration = PPX.empty_declaration ()

module String = struct
  include String
  let pp fmt s = Format.fprintf fmt "%s" s
  let show = Format.asprintf "%a" pp
end

(* Two data types, t1 and t2, each one with its own context *)

type c1 = E1 of (string[@elpi.key "t1"]) * bool
  [@@elpi.index (module String)]
[@@deriving show, elpi { declaration }]

type t1 =
  | V1 of string [@elpi.var c1]
  | A1 of t1 * t1
  | L1 of bool * string *
      (t1[@elpi.binder "t1" c1
         (fun b s -> E1(s,b))])
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
  | L2 of int * string *
      (t2[@elpi.binder "t2" c2
         (fun i s -> E2(s,i))])
[@@deriving show, elpi { declaration }]

let t2 :
    'c 'csts.
    (t2, #ctx_for_t2 as 'c, 'csts)
      ContextualConversion.t = t2


(* The context in which both t1 and t2 can be read back *)
[%%elpi.compose_ctx both [t1; t2]]

open BuiltInPredicate.Notation

(* A predicate taking in input two data living under different contexts *)
let both_to_string = BuiltInPredicate.ContextualPred("t1->t2->string",in_ctx_for_both,
  In(t1,"A",
  In(t2,"B",
  Out(BuiltInData.stringC,"S",
  Read("a t1 and a t2, each one under its own context")))),
  fun (a : t1) (b : t2) (_s : string BuiltInPredicate.oarg)
    ~depth:_ c (_cst : Data.constraints) (_state : State.t) ->

    !: (Format.asprintf "@[<hov>%a@ |-@ %a@ ;@ %a@ |-@ %a@]@\n%!"
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_c1))
        c#c1
      t1.pp a
      (RawData.Constants.Map.pp
         (PPX.pp_ctx_entry pp_c2))
        c#c2
      t2.pp b)
)

let builtin = let open BuiltIn in
  BuiltIn.declare ~file_name ((PPX.to_list declaration) @ [
    MLCode(both_to_string,DocAbove);
  ])

let program = {|
main :-
  pi x\ pi y\
    e1 x "x" tt ==>
    e2 y "y" 1 ==>
    % the bound variables are copied to themselves
    t1.copy x x ==> t2.copy y y ==> (
      sigma A B C D\
        A = (l1 tt "z" z\ a1 z x),
        B = (a2 y y),
        print {t1->t2->string A B},
        t1.copy A C,
        t2.copy B D,
        print {t1->t2->string C D}).
|}

let () = Ppx_tests_lib.run_program builtin program
