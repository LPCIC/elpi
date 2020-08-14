(*83d0917ef4644ac288b486b091a03067003847df *src/data.ml *)
#1 "src/data.ml"
module Fmt = Format
module F = Ast.Func
open Util
module Term =
  struct
    let pp_const = mk_spaghetti_printer ()
    type constant = int
    let pp_constant = pp_spaghetti pp_const
    let show_constant = show_spaghetti pp_const
    let equal_constant x y = x == y
    module Constants :
      sig
        type t = constant
        module Map : Map.S with type  key =  constant
        module Set : Set.S with type  elt =  constant
        val pp : Format.formatter -> t -> unit
        val show : t -> string
      end =
      struct
        module Self =
          struct
            type t = constant
            let compare x y = x - y
            let pp = pp_constant
            let show = show_constant
          end
        module Map = (Map.Make)(Self)
        module Set = (Set.Make)(Self)
        include Self
      end 
    let pp_oref = mk_spaghetti_printer ()
    let id_term = UUID.make ()
    type 'unification_def stuck_goal_kind = ..
    let pp_stuck_goal_kind p1 fmt x = ()
    let show_stuck_goal_kind p1 _ = ""
    let equal_stuck_goal_kind _ x y = x == y
    type 'unification_def stuck_goal_kind +=  
      | Unification of 'unification_def 
    type term =
      | Const of constant 
      | Lam of term 
      | App of constant * term * term list 
      | Cons of term * term 
      | Nil 
      | Discard 
      | Builtin of constant * term list 
      | CData of CData.t 
      | UVar of uvar_body * int * int 
      | AppUVar of uvar_body * int * term list 
      | Arg of int * int 
      | AppArg of int * term list 
    and uvar_body =
      {
      mutable contents: term [@printer pp_spaghetti_any ~id:id_term pp_oref];
      mutable rest: stuck_goal list
        [@printer fun _ -> fun _ -> ()][@equal fun _ -> fun _ -> true]}
    and stuck_goal =
      {
      mutable blockers: blockers ;
      kind: unification_def stuck_goal_kind }
    and blockers = uvar_body list
    and unification_def =
      {
      adepth: int ;
      env: term array ;
      bdepth: int ;
      a: term ;
      b: term ;
      matching: bool }
    and clause_src = {
      hdepth: int ;
      hsrc: term }
    and prolog_prog = {
      src: clause_src list ;
      index: index }
    and index = second_lvl_idx Ptmap.t
    and second_lvl_idx =
      | TwoLevelIndex of
      {
      mode: mode ;
      argno: int ;
      all_clauses: clause list ;
      flex_arg_clauses: clause list ;
      arg_idx: clause list Ptmap.t } 
      | BitHash of
      {
      mode: mode ;
      args: int list ;
      time: int ;
      args_idx: (clause * int) list Ptmap.t } 
    and clause =
      {
      depth: int ;
      args: term list ;
      hyps: term list ;
      vars: int ;
      mode: mode ;
      loc: Loc.t option }
    and mode = bool list[@@deriving show]
    let rec pp_term :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        term -> Ppx_deriving_runtime_proxy.unit
      =
      let __13 () = pp_term
      and __12 () = pp_term
      and __11 () = pp_uvar_body
      and __10 () = pp_uvar_body
      and __9 () = CData.pp
      and __8 () = pp_term
      and __7 () = pp_constant
      and __6 () = pp_term
      and __5 () = pp_term
      and __4 () = pp_term
      and __3 () = pp_term
      and __2 () = pp_constant
      and __1 () = pp_term
      and __0 () = pp_constant in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Const a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.Const@ ";
                 ((__0 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Lam a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.Lam@ ";
                 ((__1 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | App (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.App (@,";
                 ((((__2 ()) fmt) a0;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                   ((__3 ()) fmt) a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__4 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Cons (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.Cons (@,";
                 (((__5 ()) fmt) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__6 ()) fmt) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Nil ->
                Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                  "Data.Term.Nil"
            | Discard ->
                Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                  "Data.Term.Discard"
            | Builtin (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.Builtin (@,";
                 (((__7 ()) fmt) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__8 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | CData a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.CData@ ";
                 ((__9 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | UVar (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.UVar (@,";
                 ((((__10 ()) fmt) a0;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                   (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | AppUVar (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.AppUVar (@,";
                 ((((__11 ()) fmt) a0;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                   (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__12 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Arg (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.Arg (@,";
                 ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | AppArg (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.AppArg (@,";
                 ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__13 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])
    and show_term : term -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_term x[@@ocaml.warning
                                                                    "-32"]
    and pp_uvar_body :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        uvar_body -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () =
        ((let fprintf = Ppx_deriving_runtime_proxy.Format.fprintf in
          fun _ -> fun _ -> ())
        [@ocaml.warning "-26"])
      and __0 () =
        ((let fprintf = Ppx_deriving_runtime_proxy.Format.fprintf in
          pp_spaghetti_any ~id:id_term pp_oref)
        [@ocaml.warning "-26"]) in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                  "Data.Term.contents";
                ((__0 ()) fmt) x.contents;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "rest";
               ((__1 ()) fmt) x.rest;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_uvar_body : uvar_body -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_uvar_body x
    [@@ocaml.warning "-32"]
    and pp_stuck_goal :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        stuck_goal -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = pp_stuck_goal_kind
      and __1 () = pp_unification_def
      and __0 () = pp_blockers in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                  "Data.Term.blockers";
                ((__0 ()) fmt) x.blockers;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "kind";
               ((__2 ()) (fun fmt -> (__1 ()) fmt) fmt) x.kind;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_stuck_goal : stuck_goal -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_stuck_goal x
    [@@ocaml.warning "-32"]
    and pp_blockers :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        blockers -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_uvar_body in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
              ignore
                (List.fold_left
                   (fun sep ->
                      fun x ->
                        if sep
                        then Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                        ((__0 ()) fmt) x;
                        true) false x);
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")
        [@ocaml.warning "-A"])
    and show_blockers : blockers -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_blockers x
    [@@ocaml.warning "-32"]
    and pp_unification_def :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        unification_def -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = pp_term
      and __1 () = pp_term
      and __0 () = pp_term in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "Data.Term.adepth";
                    (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.adepth;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "env";
                   ((fun x ->
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[|";
                       ignore
                         (Array.fold_left
                            (fun sep ->
                               fun x ->
                                 if sep
                                 then
                                   Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                     ";@ ";
                                 ((__0 ()) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,|]@]"))
                     x.env;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "bdepth";
                  (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.bdepth;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "a";
                 ((__1 ()) fmt) x.a;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "b";
                ((__2 ()) fmt) x.b;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "matching";
               (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%B") x.matching;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_unification_def : unification_def -> Ppx_deriving_runtime_proxy.string
      =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_unification_def x
    [@@ocaml.warning "-32"]
    and pp_clause_src :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        clause_src -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_term in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                  "Data.Term.hdepth";
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.hdepth;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "hsrc";
               ((__0 ()) fmt) x.hsrc;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_clause_src : clause_src -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_clause_src x
    [@@ocaml.warning "-32"]
    and pp_prolog_prog :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        prolog_prog -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () = pp_index
      and __0 () = pp_clause_src in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                  "Data.Term.src";
                ((fun x ->
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                    ignore
                      (List.fold_left
                         (fun sep ->
                            fun x ->
                              if sep
                              then
                                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                              ((__0 ()) fmt) x;
                              true) false x);
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) 
                  x.src;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "index";
               ((__1 ()) fmt) x.index;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_prolog_prog : prolog_prog -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_prolog_prog x
    [@@ocaml.warning "-32"]
    and pp_index :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        index -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () = Ptmap.pp
      and __0 () = pp_second_lvl_idx in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt -> (__1 ()) (fun fmt -> (__0 ()) fmt) fmt)
        [@ocaml.warning "-A"])
    and show_index : index -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_index x[@@ocaml.warning
                                                                    "-32"]
    and pp_second_lvl_idx :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        second_lvl_idx -> Ppx_deriving_runtime_proxy.unit
      =
      let __7 () = Ptmap.pp
      and __6 () = pp_clause
      and __5 () = pp_mode
      and __4 () = Ptmap.pp
      and __3 () = pp_clause
      and __2 () = pp_clause
      and __1 () = pp_clause
      and __0 () = pp_mode in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | TwoLevelIndex
                { mode = amode; argno = aargno; all_clauses = aall_clauses;
                  flex_arg_clauses = aflex_arg_clauses; arg_idx = aarg_idx }
                ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "@[<2>Data.Term.TwoLevelIndex {@,";
                 (((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                        "mode";
                      ((__0 ()) fmt) amode;
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "argno";
                     (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") aargno;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "all_clauses";
                    ((fun x ->
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                        ignore
                          (List.fold_left
                             (fun sep ->
                                fun x ->
                                  if sep
                                  then
                                    Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                      ";@ ";
                                  ((__1 ()) fmt) x;
                                  true) false x);
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                      aall_clauses;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                     "flex_arg_clauses";
                   ((fun x ->
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                       ignore
                         (List.fold_left
                            (fun sep ->
                               fun x ->
                                 if sep
                                 then
                                   Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                     ";@ ";
                                 ((__2 ()) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                     aflex_arg_clauses;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                    "arg_idx";
                  ((__4 ())
                     (fun fmt ->
                        fun x ->
                          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                          ignore
                            (List.fold_left
                               (fun sep ->
                                  fun x ->
                                    if sep
                                    then
                                      Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                        ";@ ";
                                    ((__3 ()) fmt) x;
                                    true) false x);
                          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")
                     fmt) aarg_idx;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]}")
            | BitHash
                { mode = amode; args = aargs; time = atime;
                  args_idx = aargs_idx }
                ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "@[<2>Data.Term.BitHash {@,";
                 ((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "mode";
                     ((__5 ()) fmt) amode;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "args";
                    ((fun x ->
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                        ignore
                          (List.fold_left
                             (fun sep ->
                                fun x ->
                                  if sep
                                  then
                                    Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                      ";@ ";
                                  (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                     "%d") x;
                                  true) false x);
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                      aargs;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "time";
                   (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") atime;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                    "args_idx";
                  ((__7 ())
                     (fun fmt ->
                        fun x ->
                          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                          ignore
                            (List.fold_left
                               (fun sep ->
                                  fun x ->
                                    if sep
                                    then
                                      Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                        ";@ ";
                                    ((fun (a0, a1) ->
                                        Ppx_deriving_runtime_proxy.Format.fprintf
                                          fmt "(@[";
                                        (((__6 ()) fmt) a0;
                                         Ppx_deriving_runtime_proxy.Format.fprintf
                                           fmt ",@ ";
                                         (Ppx_deriving_runtime_proxy.Format.fprintf
                                            fmt "%d") a1);
                                        Ppx_deriving_runtime_proxy.Format.fprintf
                                          fmt "@])")) x;
                                    true) false x);
                          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")
                     fmt) aargs_idx;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]}"))
        [@ocaml.warning "-A"])
    and show_second_lvl_idx : second_lvl_idx -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_second_lvl_idx x
    [@@ocaml.warning "-32"]
    and pp_clause :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        clause -> Ppx_deriving_runtime_proxy.unit
      =
      let __3 () = Loc.pp
      and __2 () = pp_mode
      and __1 () = pp_term
      and __0 () = pp_term in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "Data.Term.depth";
                    (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.depth;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "args";
                   ((fun x ->
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                       ignore
                         (List.fold_left
                            (fun sep ->
                               fun x ->
                                 if sep
                                 then
                                   Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                     ";@ ";
                                 ((__0 ()) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                     x.args;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "hyps";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__1 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                    x.hyps;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "vars";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.vars;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "mode";
                ((__2 ()) fmt) x.mode;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "loc";
               ((function
                 | None ->
                     Ppx_deriving_runtime_proxy.Format.pp_print_string fmt "None"
                 | Some x ->
                     (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                        "(Some ";
                      ((__3 ()) fmt) x;
                      Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                 x.loc;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_clause : clause -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_clause x[@@ocaml.warning
                                                                    "-32"]
    and (pp_mode :
          Ppx_deriving_runtime_proxy.Format.formatter ->
            mode -> Ppx_deriving_runtime_proxy.unit)
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
              ignore
                (List.fold_left
                   (fun sep ->
                      fun x ->
                        if sep
                        then Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                        (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%B") x;
                        true) false x);
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")
      [@ocaml.warning "-A"])
    and show_mode : mode -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_mode x[@@ocaml.warning
                                                                    "-32"]
    type constraints = stuck_goal list
    type hyps = clause_src list
    type extra_goals = term list
    type suspended_goal = {
      context: hyps ;
      goal: (int * term) }
    type indexing =
      | MapOn of int 
      | Hash of int list [@@deriving show]
    let rec pp_indexing :
              Ppx_deriving_runtime_proxy.Format.formatter ->
                indexing -> Ppx_deriving_runtime_proxy.unit
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | MapOn a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.MapOn@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Hash a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Term.Hash@ ";
                 ((fun x ->
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                     ignore
                       (List.fold_left
                          (fun sep ->
                             fun x ->
                               if sep
                               then
                                 Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                   ";@ ";
                               (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d")
                                 x;
                               true) false x);
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])
    and show_indexing : indexing -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_indexing x
    [@@ocaml.warning "-32"]
    let mkLam x = Lam x[@@inline ]
    let mkApp c x xs = App (c, x, xs)[@@inline ]
    let mkCons hd tl = Cons (hd, tl)[@@inline ]
    let mkNil = Nil
    let mkDiscard = Discard
    let mkBuiltin c args = Builtin (c, args)[@@inline ]
    let mkCData c = CData c[@@inline ]
    let mkUVar r d ano = UVar (r, d, ano)[@@inline ]
    let mkAppUVar r d args = AppUVar (r, d, args)[@@inline ]
    let mkArg i ano = Arg (i, ano)[@@inline ]
    let mkAppArg i args = AppArg (i, args)[@@inline ]
    module C =
      struct
        let { CData.cin = in_int; isc = is_int; cout = out_int } as int =
          Ast.cint
        let is_int = is_int
        let to_int = out_int
        let of_int x = CData (in_int x)
        let { CData.cin = in_float; isc = is_float; cout = out_float } as
              float
          = Ast.cfloat
        let is_float = is_float
        let to_float = out_float
        let of_float x = CData (in_float x)
        let { CData.cin = in_string; isc = is_string; cout = out_string } as
              string
          = Ast.cstring
        let is_string = is_string
        let to_string x = out_string x
        let of_string x = CData (in_string x)
        let loc = Ast.cloc
        let is_loc = loc.CData.isc
        let to_loc = loc.CData.cout
        let of_loc x = CData (loc.CData.cin x)
      end
    let destConst = function | Const x -> x | _ -> assert false
    let oref x = { contents = x; rest = [] }
    let (!!) { contents = x } = x
    type env = term array
    let empty_env = [||]
  end
include Term
module State :
  sig
    type 'a component
    val declare :
      name:string ->
        pp:(Format.formatter -> 'a -> unit) ->
          init:(unit -> 'a) ->
            clause_compilation_is_over:('a -> 'a) ->
              goal_compilation_is_over:(args:uvar_body StrMap.t ->
                                          'a -> 'a option)
                ->
                compilation_is_over:('a -> 'a option) ->
                  execution_is_over:('a -> 'a option) -> 'a component
    type t
    val init : unit -> t
    val end_clause_compilation : t -> t
    val end_goal_compilation : uvar_body StrMap.t -> t -> t
    val end_compilation : t -> t
    val end_execution : t -> t
    val get : 'a component -> t -> 'a
    val set : 'a component -> t -> 'a -> t
    val drop : 'a component -> t -> t
    val update : 'a component -> t -> ('a -> 'a) -> t
    val update_return : 'a component -> t -> ('a -> ('a * 'b)) -> (t * 'b)
    val pp : Format.formatter -> t -> unit
  end =
  struct
    type t = Obj.t StrMap.t
    type 'a component = string
    type extension =
      {
      init: unit -> Obj.t ;
      end_clause: Obj.t -> Obj.t ;
      end_goal: args:uvar_body StrMap.t -> Obj.t -> Obj.t option ;
      end_comp: Obj.t -> Obj.t option ;
      end_exec: Obj.t -> Obj.t option ;
      pp: Format.formatter -> Obj.t -> unit }
    let extensions : extension StrMap.t ref = ref StrMap.empty
    let get name t =
      try Obj.obj (StrMap.find name t)
      with
      | Not_found ->
          anomaly ("State.get: component " ^ (name ^ " not found"))
    let set name t v = StrMap.add name (Obj.repr v) t
    let drop name t = StrMap.remove name t
    let update name t f =
      StrMap.add name (Obj.repr (f (Obj.obj (StrMap.find name t)))) t
    let update_return name t f =
      let x = get name t in
      let (x, res) = f x in let t = set name t x in (t, res)
    let declare ~name  ~pp  ~init  ~clause_compilation_is_over 
      ~goal_compilation_is_over  ~compilation_is_over  ~execution_is_over  =
      if StrMap.mem name (!extensions)
      then anomaly ("Extension " ^ (name ^ " already declared"));
      extensions :=
        (StrMap.add name
           {
             init = (fun x -> Obj.repr (init x));
             pp = (fun fmt -> fun x -> pp fmt (Obj.obj x));
             end_goal =
               (fun ~args ->
                  fun x ->
                    option_map Obj.repr
                      (goal_compilation_is_over ~args (Obj.obj x)));
             end_clause =
               (fun x -> Obj.repr (clause_compilation_is_over (Obj.obj x)));
             end_comp =
               (fun x ->
                  option_map Obj.repr (compilation_is_over (Obj.obj x)));
             end_exec =
               (fun x -> option_map Obj.repr (execution_is_over (Obj.obj x)))
           } (!extensions));
      name
    let init () =
      StrMap.fold (fun name -> fun { init } -> StrMap.add name (init ()))
        (!extensions) StrMap.empty
    let end_clause_compilation m =
      StrMap.fold
        (fun name ->
           fun obj ->
             fun acc ->
               let o = (StrMap.find name (!extensions)).end_clause obj in
               StrMap.add name o acc) m StrMap.empty
    let end_goal_compilation args m =
      StrMap.fold
        (fun name ->
           fun obj ->
             fun acc ->
               match (StrMap.find name (!extensions)).end_goal ~args obj with
               | None -> acc
               | Some o -> StrMap.add name o acc) m StrMap.empty
    let end_compilation m =
      StrMap.fold
        (fun name ->
           fun obj ->
             fun acc ->
               match (StrMap.find name (!extensions)).end_comp obj with
               | None -> acc
               | Some o -> StrMap.add name o acc) m StrMap.empty
    let end_execution m =
      StrMap.fold
        (fun name ->
           fun obj ->
             fun acc ->
               match (StrMap.find name (!extensions)).end_exec obj with
               | None -> acc
               | Some o -> StrMap.add name o acc) m StrMap.empty
    let pp fmt t =
      StrMap.iter
        (fun name ->
           fun { pp } ->
             try pp fmt (StrMap.find name t) with | Not_found -> ())
        (!extensions)
  end 
module Global_symbols :
  sig
    type t =
      {
      mutable s2c: constant StrMap.t ;
      mutable c2s: string Constants.Map.t ;
      mutable last_global: int }
    val table : t
    val declare_global_symbol : string -> constant
    val cutc : constant
    val andc : constant
    val orc : constant
    val implc : constant
    val rimplc : constant
    val pic : constant
    val sigmac : constant
    val eqc : constant
    val rulec : constant
    val consc : constant
    val nilc : constant
    val entailsc : constant
    val nablac : constant
    val asc : constant
    val arrowc : constant
    val uvarc : constant
    val propc : constant
    val ctypec : constant
    val variadic : constant
    val spillc : constant
    val truec : constant
    val declare_constraintc : constant
    val print_constraintsc : constant
  end =
  struct
    type t =
      {
      mutable s2c: constant StrMap.t ;
      mutable c2s: string Constants.Map.t ;
      mutable last_global: int }[@@deriving show]
    let rec pp :
      Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = Constants.Map.pp
      and __1 () = StrMap.pp
      and __0 () = pp_constant in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "Data.Global_symbols.s2c";
                 ((__1 ()) (fun fmt -> (__0 ()) fmt) fmt) x.s2c;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "c2s";
                ((__2 ())
                   (fun fmt -> Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S")
                   fmt) x.c2s;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                 "last_global";
               (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.last_global;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show : t -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp x[@@ocaml.warning
                                                               "-32"]
    let table =
      { last_global = 0; s2c = StrMap.empty; c2s = Constants.Map.empty }
    let declare_global_symbol x =
      try StrMap.find x table.s2c
      with
      | Not_found ->
          (table.last_global <- (table.last_global - 1);
           (let n = table.last_global in
            table.s2c <- (StrMap.add x n table.s2c);
            table.c2s <- (Constants.Map.add n x table.c2s);
            n))
    let andc = declare_global_symbol (let open F in show andf)
    let arrowc = declare_global_symbol (let open F in show arrowf)
    let asc = declare_global_symbol "as"
    let consc = declare_global_symbol (let open F in show consf)
    let cutc = declare_global_symbol (let open F in show cutf)
    let entailsc = declare_global_symbol "?-"
    let eqc = declare_global_symbol (let open F in show eqf)
    let uvarc = declare_global_symbol "uvar"
    let implc = declare_global_symbol (let open F in show implf)
    let nablac = declare_global_symbol "nabla"
    let nilc = declare_global_symbol (let open F in show nilf)
    let orc = declare_global_symbol (let open F in show orf)
    let pic = declare_global_symbol (let open F in show pif)
    let rimplc = declare_global_symbol (let open F in show rimplf)
    let rulec = declare_global_symbol "rule"
    let sigmac = declare_global_symbol (let open F in show sigmaf)
    let spillc = declare_global_symbol (let open F in show spillf)
    let truec = declare_global_symbol (let open F in show truef)
    let ctypec = declare_global_symbol (let open F in show ctypef)
    let propc = declare_global_symbol "prop"
    let variadic = declare_global_symbol "variadic"
    let declare_constraintc = declare_global_symbol "declare_constraint"
    let print_constraintsc = declare_global_symbol "print_constraints"
  end 
let dummy = App (Global_symbols.cutc, (Const Global_symbols.cutc), [])
module CHR :
  sig
    type t
    type clique
    type sequent = {
      eigen: term ;
      context: term ;
      conclusion: term }
    and rule =
      {
      to_match: sequent list ;
      to_remove: sequent list ;
      patsno: int ;
      guard: term option ;
      new_goal: sequent option ;
      nargs: int [@default 0];
      pattern: constant list ;
      rule_name: string }
    val pp_sequent : Fmt.formatter -> sequent -> unit
    val show_sequent : sequent -> string
    val pp_rule : Fmt.formatter -> rule -> unit
    val show_rule : rule -> string
    val empty : t
    val new_clique :
      (constant -> string) -> constant list -> t -> (t * clique)
    val clique_of : constant -> t -> Constants.Set.t option
    val add_rule : clique -> rule -> t -> t
    val in_clique : clique -> constant -> bool
    val rules_for : constant -> t -> rule list
    val pp : Fmt.formatter -> t -> unit
    val show : t -> string
  end =
  struct
    type sequent = {
      eigen: term ;
      context: term ;
      conclusion: term }
    and rule =
      {
      to_match: sequent list ;
      to_remove: sequent list ;
      patsno: int ;
      guard: term option ;
      new_goal: sequent option ;
      nargs: int [@default 0];
      pattern: constant list ;
      rule_name: string }[@@deriving show]
    let rec pp_sequent :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        sequent -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = pp_term
      and __1 () = pp_term
      and __0 () = pp_term in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "Data.CHR.eigen";
                 ((__0 ()) fmt) x.eigen;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "context";
                ((__1 ()) fmt) x.context;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                 "conclusion";
               ((__2 ()) fmt) x.conclusion;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_sequent : sequent -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_sequent x
    [@@ocaml.warning "-32"]
    and pp_rule :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        rule -> Ppx_deriving_runtime_proxy.unit
      =
      let __4 () = pp_constant
      and __3 () = pp_sequent
      and __2 () = pp_term
      and __1 () = pp_sequent
      and __0 () = pp_sequent in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((((((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                        "Data.CHR.to_match";
                      ((fun x ->
                          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                          ignore
                            (List.fold_left
                               (fun sep ->
                                  fun x ->
                                    if sep
                                    then
                                      Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                        ";@ ";
                                    ((__0 ()) fmt) x;
                                    true) false x);
                          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                        x.to_match;
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "to_remove";
                     ((fun x ->
                         Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                         ignore
                           (List.fold_left
                              (fun sep ->
                                 fun x ->
                                   if sep
                                   then
                                     Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                       ";@ ";
                                   ((__1 ()) fmt) x;
                                   true) false x);
                         Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                       x.to_remove;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "patsno";
                    (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.patsno;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "guard";
                   ((function
                     | None ->
                         Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                           "None"
                     | Some x ->
                         (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                            "(Some ";
                          ((__2 ()) fmt) x;
                          Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                     x.guard;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                    "new_goal";
                  ((function
                    | None ->
                        Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                          "None"
                    | Some x ->
                        (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                           "(Some ";
                         ((__3 ()) fmt) x;
                         Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                    x.new_goal;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "nargs";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.nargs;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "pattern";
                ((fun x ->
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                    ignore
                      (List.fold_left
                         (fun sep ->
                            fun x ->
                              if sep
                              then
                                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                              ((__4 ()) fmt) x;
                              true) false x);
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                  x.pattern;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "rule_name";
               (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x.rule_name;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_rule : rule -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_rule x[@@ocaml.warning
                                                                    "-32"]
    type t =
      {
      cliques: Constants.Set.t Constants.Map.t ;
      rules: rule list Constants.Map.t }[@@deriving show]
    let rec pp :
      Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
      =
      let __3 () = Constants.Map.pp
      and __2 () = pp_rule
      and __1 () = Constants.Map.pp
      and __0 () = Constants.Set.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                  "Data.CHR.cliques";
                ((__1 ()) (fun fmt -> (__0 ()) fmt) fmt) x.cliques;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "rules";
               ((__3 ())
                  (fun fmt ->
                     fun x ->
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                       ignore
                         (List.fold_left
                            (fun sep ->
                               fun x ->
                                 if sep
                                 then
                                   Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                     ";@ ";
                                 ((__2 ()) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]") fmt)
                 x.rules;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show : t -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp x[@@ocaml.warning
                                                               "-32"]
    type clique = Constants.Set.t
    let empty =
      { cliques = Constants.Map.empty; rules = Constants.Map.empty }
    let in_clique m c = Constants.Set.mem c m
    let new_clique show_constant cl ({ cliques } as chr) =
      if cl = [] then error "empty clique";
      (let c = List.fold_right Constants.Set.add cl Constants.Set.empty in
       Constants.Map.iter
         (fun _ ->
            fun c' ->
              if
                (not (Constants.Set.is_empty (Constants.Set.inter c c'))) &&
                  (not (Constants.Set.equal c c'))
              then
                error
                  ("overlapping constraint cliques: {" ^
                     ((String.concat ","
                         (List.map show_constant (Constants.Set.elements c)))
                        ^
                        ("} {" ^
                           ((String.concat ","
                               (List.map show_constant
                                  (Constants.Set.elements c')))
                              ^ "}"))))) cliques;
       (let cliques =
          List.fold_right
            (fun x -> fun cliques -> Constants.Map.add x c cliques) cl
            cliques in
        ({ chr with cliques }, c)))
    let clique_of c { cliques } =
      try Some (Constants.Map.find c cliques) with | Not_found -> None
    let add_rule cl r ({ rules } as chr) =
      let rules =
        Constants.Set.fold
          (fun c ->
             fun rules ->
               try
                 let rs = Constants.Map.find c rules in
                 Constants.Map.add c (rs @ [r]) rules
               with | Not_found -> Constants.Map.add c [r] rules) cl rules in
      { chr with rules }
    let rules_for c { rules } =
      try Constants.Map.find c rules with | Not_found -> []
  end 
type clause_w_info =
  {
  clloc: CData.t ;
  clargsname: string list ;
  clbody: clause }[@@deriving show]
let rec pp_clause_w_info :
  Ppx_deriving_runtime_proxy.Format.formatter ->
    clause_w_info -> Ppx_deriving_runtime_proxy.unit
  =
  let __1 () = pp_clause
  and __0 () = CData.pp in
  ((let open! Ppx_deriving_runtime_proxy in
      fun fmt ->
        fun x ->
          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
          (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "Data.clloc";
             ((__0 ()) fmt) x.clloc;
             Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
            Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
            Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "clargsname";
            ((fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                ignore
                  (List.fold_left
                     (fun sep ->
                        fun x ->
                          if sep
                          then Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                          (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x;
                          true) false x);
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
              x.clargsname;
            Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
           Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
           Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "clbody";
           ((__1 ()) fmt) x.clbody;
           Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
    [@ocaml.warning "-A"])
and show_clause_w_info : clause_w_info -> Ppx_deriving_runtime_proxy.string =
  fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_clause_w_info x
[@@ocaml.warning "-32"]
type macro_declaration = (Ast.Term.t * Loc.t) F.Map.t[@@deriving show]
let rec pp_macro_declaration :
  Ppx_deriving_runtime_proxy.Format.formatter ->
    macro_declaration -> Ppx_deriving_runtime_proxy.unit
  =
  let __2 () = F.Map.pp
  and __1 () = Loc.pp
  and __0 () = Ast.Term.pp in
  ((let open! Ppx_deriving_runtime_proxy in
      fun fmt ->
        (__2 ())
          (fun fmt ->
             fun (a0, a1) ->
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "(@[";
               (((__0 ()) fmt) a0;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                ((__1 ()) fmt) a1);
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])") fmt)
    [@ocaml.warning "-A"])
and show_macro_declaration : macro_declaration -> Ppx_deriving_runtime_proxy.string
  = fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_macro_declaration x
[@@ocaml.warning "-32"]
exception No_clause 
exception No_more_steps 
module Conversion =
  struct
    type ty_ast =
      | TyName of string 
      | TyApp of string * ty_ast * ty_ast list [@@deriving show]
    let rec pp_ty_ast :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        ty_ast -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () = pp_ty_ast
      and __0 () = pp_ty_ast in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | TyName a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Conversion.TyName@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | TyApp (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Data.Conversion.TyApp (@,";
                 (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                   ((__0 ()) fmt) a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__1 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])
    and show_ty_ast : ty_ast -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_ty_ast x[@@ocaml.warning
                                                                    "-32"]
    type 'a embedding =
      depth:int -> State.t -> 'a -> (State.t * term * extra_goals)
    type 'a readback =
      depth:int -> State.t -> term -> (State.t * 'a * extra_goals)
    type 'a t =
      {
      ty: ty_ast ;
      pp_doc: Format.formatter -> unit -> unit [@opaque ];
      pp: Format.formatter -> 'a -> unit [@opaque ];
      embed: 'a embedding [@opaque ];
      readback: 'a readback [@opaque ]}[@@deriving show]
    let rec pp :
      'a .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'a -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            'a t -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_ty_ast in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_a ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                (((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "Data.Conversion.ty";
                     ((__0 ()) fmt) x.ty;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "pp_doc";
                    ((fun _ ->
                        Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                          "<opaque>")) x.pp_doc;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "pp";
                   ((fun _ ->
                       Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                         "<opaque>")) x.pp;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "embed";
                  ((fun _ ->
                      Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                        "<opaque>")) x.embed;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "readback";
                 ((fun _ ->
                     Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                       "<opaque>")) x.readback;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'a .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'a -> Ppx_deriving_runtime_proxy.unit)
          -> 'a t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_a ->
        fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" (pp poly_a) x
    [@@ocaml.warning "-32"]
    exception TypeErr of ty_ast * int * term 
    let rec show_ty_ast ?(outer= true)  =
      function
      | TyName s -> s
      | TyApp (s, x, xs) ->
          let t =
            String.concat " " (s ::
              (List.map (show_ty_ast ~outer:false) (x :: xs))) in
          if outer then t else "(" ^ (t ^ ")")
  end
module ContextualConversion =
  struct
    type ty_ast = Conversion.ty_ast =
      | TyName of string 
      | TyApp of string * ty_ast * ty_ast list [@@deriving show]
    let rec pp_ty_ast :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        ty_ast -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () = pp_ty_ast
      and __0 () = pp_ty_ast in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | TyName a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Conversion.TyName@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | TyApp (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Conversion.TyApp (@,";
                 (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                   ((__0 ()) fmt) a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__1 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])
    and show_ty_ast : ty_ast -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_ty_ast x[@@ocaml.warning
                                                                    "-32"]
    type ('a, 'hyps, 'constraints) embedding =
      depth:int ->
        'hyps ->
          'constraints -> State.t -> 'a -> (State.t * term * extra_goals)
    type ('a, 'hyps, 'constraints) readback =
      depth:int ->
        'hyps ->
          'constraints -> State.t -> term -> (State.t * 'a * extra_goals)
    type ('a, 'hyps, 'constraints) t =
      {
      ty: ty_ast ;
      pp_doc: Format.formatter -> unit -> unit [@opaque ];
      pp: Format.formatter -> 'a -> unit [@opaque ];
      embed: ('a, 'hyps, 'constraints) embedding [@opaque ];
      readback: ('a, 'hyps, 'constraints) readback [@opaque ]}[@@deriving
                                                                show]
    let rec pp :
      'a 'hyps 'constraints .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'a -> Ppx_deriving_runtime_proxy.unit)
          ->
          (Ppx_deriving_runtime_proxy.Format.formatter ->
             'hyps -> Ppx_deriving_runtime_proxy.unit)
            ->
            (Ppx_deriving_runtime_proxy.Format.formatter ->
               'constraints -> Ppx_deriving_runtime_proxy.unit)
              ->
              Ppx_deriving_runtime_proxy.Format.formatter ->
                ('a, 'hyps, 'constraints) t -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_ty_ast in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_a ->
            fun poly_hyps ->
              fun poly_constraints ->
                fun fmt ->
                  fun x ->
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                    (((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                           "Data.ContextualConversion.ty";
                         ((__0 ()) fmt) x.ty;
                         Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                          "pp_doc";
                        ((fun _ ->
                            Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                              "<opaque>")) x.pp_doc;
                        Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                         "pp";
                       ((fun _ ->
                           Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                             "<opaque>")) x.pp;
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                        "embed";
                      ((fun _ ->
                          Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                            "<opaque>")) x.embed;
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "readback";
                     ((fun _ ->
                         Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                           "<opaque>")) x.readback;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'a 'hyps 'constraints .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'a -> Ppx_deriving_runtime_proxy.unit)
          ->
          (Ppx_deriving_runtime_proxy.Format.formatter ->
             'hyps -> Ppx_deriving_runtime_proxy.unit)
            ->
            (Ppx_deriving_runtime_proxy.Format.formatter ->
               'constraints -> Ppx_deriving_runtime_proxy.unit)
              -> ('a, 'hyps, 'constraints) t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_a ->
        fun poly_hyps ->
          fun poly_constraints ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.asprintf "%a"
                (((pp poly_a) poly_hyps) poly_constraints) x[@@ocaml.warning
                                                              "-32"]
    type ('hyps, 'constraints) ctx_readback =
      depth:int ->
        hyps ->
          constraints ->
            State.t -> (State.t * 'hyps * 'constraints * extra_goals)
    let unit_ctx : (unit, unit) ctx_readback =
      fun ~depth:_ -> fun _ -> fun _ -> fun s -> (s, (), (), [])
    let raw_ctx : (hyps, constraints) ctx_readback =
      fun ~depth:_ -> fun h -> fun c -> fun s -> (s, h, c, [])
    let (!<) { ty; pp_doc; pp; embed; readback } =
      {
        Conversion.ty = ty;
        pp;
        pp_doc;
        embed = (fun ~depth -> fun s -> fun t -> embed ~depth () () s t);
        readback =
          (fun ~depth -> fun s -> fun t -> readback ~depth () () s t)
      }
    let (!>) { Conversion.ty = ty; pp_doc; pp; embed; readback } =
      {
        ty;
        pp;
        pp_doc;
        embed =
          (fun ~depth -> fun _ -> fun _ -> fun s -> fun t -> embed ~depth s t);
        readback =
          (fun ~depth ->
             fun _ -> fun _ -> fun s -> fun t -> readback ~depth s t)
      }
    let (!>>) (f : 'a Conversion.t -> 'b Conversion.t) cc =
      let mk h c { ty; pp_doc; pp; embed; readback } =
        {
          Conversion.ty = ty;
          pp;
          pp_doc;
          embed = (fun ~depth -> fun s -> fun t -> embed ~depth h c s t);
          readback =
            (fun ~depth -> fun s -> fun t -> readback ~depth h c s t)
        } in
      let mk_pp { ty; pp_doc; pp } =
        {
          Conversion.ty = ty;
          pp;
          pp_doc;
          embed = (fun ~depth -> fun s -> fun t -> assert false);
          readback = (fun ~depth -> fun s -> fun t -> assert false)
        } in
      let { Conversion.ty = ty; pp; pp_doc } = f (mk_pp cc) in
      {
        ty;
        pp;
        pp_doc;
        embed =
          (fun ~depth ->
             fun h ->
               fun c -> fun s -> fun t -> (f (mk h c cc)).embed ~depth s t);
        readback =
          (fun ~depth ->
             fun h ->
               fun c -> fun s -> fun t -> (f (mk h c cc)).readback ~depth s t)
      }
    let (!>>>) (f : 'a Conversion.t -> 'b Conversion.t -> 'c Conversion.t) cc
      dd =
      let mk h c { ty; pp_doc; pp; embed; readback } =
        {
          Conversion.ty = ty;
          pp;
          pp_doc;
          embed = (fun ~depth -> fun s -> fun t -> embed ~depth h c s t);
          readback =
            (fun ~depth -> fun s -> fun t -> readback ~depth h c s t)
        } in
      let mk_pp { ty; pp_doc; pp } =
        {
          Conversion.ty = ty;
          pp;
          pp_doc;
          embed = (fun ~depth -> fun s -> fun t -> assert false);
          readback = (fun ~depth -> fun s -> fun t -> assert false)
        } in
      let { Conversion.ty = ty; pp; pp_doc } = f (mk_pp cc) (mk_pp dd) in
      {
        ty;
        pp;
        pp_doc;
        embed =
          (fun ~depth ->
             fun h ->
               fun c ->
                 fun s ->
                   fun t -> (f (mk h c cc) (mk h c dd)).embed ~depth s t);
        readback =
          (fun ~depth ->
             fun h ->
               fun c ->
                 fun s ->
                   fun t -> (f (mk h c cc) (mk h c dd)).readback ~depth s t)
      }
  end
let while_compiling =
  State.declare ~name:"elpi:compiling" ~pp:(fun fmt -> fun _ -> ())
    ~clause_compilation_is_over:(fun b -> b)
    ~goal_compilation_is_over:(fun ~args:_ -> fun b -> Some b)
    ~compilation_is_over:(fun _ -> Some false)
    ~execution_is_over:(fun _ -> None) ~init:(fun () -> false)
module BuiltInPredicate =
  struct
    type name = string
    type doc = string
    type 'a oarg =
      | Keep 
      | Discard 
    type 'a ioarg =
      | Data of 'a 
      | NoData 
    type ('function_type, 'inernal_outtype_in, 'internal_hyps,
      'internal_constraints) ffi =
      | In: 't Conversion.t * doc * ('i, 'o, 'h, 'c) ffi -> ('t -> 'i, 
      'o, 'h, 'c) ffi 
      | Out: 't Conversion.t * doc * ('i, ('o * 't option), 'h, 'c) ffi ->
      ('t oarg -> 'i, 'o, 'h, 'c) ffi 
      | InOut: 't ioarg Conversion.t * doc * ('i, ('o * 't option), 'h, 
      'c) ffi -> ('t ioarg -> 'i, 'o, 'h, 'c) ffi 
      | CIn: ('t, 'h, 'c) ContextualConversion.t * doc * ('i, 'o, 'h, 
      'c) ffi -> ('t -> 'i, 'o, 'h, 'c) ffi 
      | COut: ('t, 'h, 'c) ContextualConversion.t * doc * ('i,
      ('o * 't option), 'h, 'c) ffi -> ('t oarg -> 'i, 'o, 'h, 'c) ffi 
      | CInOut: ('t ioarg, 'h, 'c) ContextualConversion.t * doc * ('i,
      ('o * 't option), 'h, 'c) ffi -> ('t ioarg -> 'i, 'o, 'h, 'c) ffi 
      | Easy: doc -> (depth:int -> 'o, 'o, unit, unit) ffi 
      | Read: ('h, 'c) ContextualConversion.ctx_readback * doc ->
      (depth:int -> 'h -> 'c -> State.t -> 'o, 'o, 'h, 'c) ffi 
      | Full: ('h, 'c) ContextualConversion.ctx_readback * doc ->
      (depth:int -> 'h -> 'c -> State.t -> (State.t * 'o * extra_goals), 
      'o, 'h, 'c) ffi 
      | VariadicIn: ('h, 'c) ContextualConversion.ctx_readback * ('t, 
      'h, 'c) ContextualConversion.t * doc ->
      ('t list -> depth:int -> 'h -> 'c -> State.t -> (State.t * 'o), 
      'o, 'h, 'c) ffi 
      | VariadicOut: ('h, 'c) ContextualConversion.ctx_readback * ('t, 
      'h, 'c) ContextualConversion.t * doc ->
      ('t oarg list ->
         depth:int ->
           'h -> 'c -> State.t -> (State.t * ('o * 't option list option)),
      'o, 'h, 'c) ffi 
      | VariadicInOut: ('h, 'c) ContextualConversion.ctx_readback *
      ('t ioarg, 'h, 'c) ContextualConversion.t * doc ->
      ('t ioarg list ->
         depth:int ->
           'h -> 'c -> State.t -> (State.t * ('o * 't option list option)),
      'o, 'h, 'c) ffi 
    type t =
      | Pred: name * ('a, unit, 'h, 'c) ffi * 'a -> t 
    type doc_spec =
      | DocAbove 
      | DocNext 
    let pp_comment fmt doc =
      Fmt.fprintf fmt "@?";
      (let orig_out = Fmt.pp_get_formatter_out_functions fmt () in
       Fmt.pp_set_formatter_out_functions fmt
         {
           orig_out with
           Fmt.out_newline = (fun () -> orig_out.Fmt.out_string "\n% " 0 3)
         };
       Fmt.fprintf fmt "@[<hov>";
       Fmt.pp_print_text fmt doc;
       Fmt.fprintf fmt "@]@?";
       Fmt.pp_set_formatter_out_functions fmt orig_out)
    let pp_ty sep fmt (_, s, _) = Fmt.fprintf fmt " %s%s" s sep
    let pp_ty_args = pplist (pp_ty "") " ->" ~pplastelem:(pp_ty "")
    module ADT =
      struct
        type ('match_stateful_t, 'match_t, 't) match_t =
          | M of (ok:'match_t -> ko:(unit -> term) -> 't -> term) 
          | MS of
          (ok:'match_stateful_t ->
             ko:(State.t -> (State.t * term * extra_goals)) ->
               't -> State.t -> (State.t * term * extra_goals))
          
        type ('build_stateful_t, 'build_t) build_t =
          | B of 'build_t 
          | BS of 'build_stateful_t 
        type ('stateful_builder, 'builder, 'stateful_matcher, 'matcher,
          'self, 'hyps, 'constraints) constructor_arguments =
          | N: (State.t -> (State.t * 'self), 'self,
          State.t -> (State.t * term * extra_goals), term, 'self, 'hyps,
          'constraints) constructor_arguments 
          | A: 'a Conversion.t * ('bs, 'b, 'ms, 'm, 'self, 'hyps,
          'constraints) constructor_arguments -> ('a -> 'bs, 'a -> 'b,
          'a -> 'ms, 'a -> 'm, 'self, 'hyps, 'constraints)
          constructor_arguments 
          | CA: ('a, 'hyps, 'constraints) ContextualConversion.t * ('bs, 
          'b, 'ms, 'm, 'self, 'hyps, 'constraints) constructor_arguments ->
          ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm, 'self, 'hyps,
          'constraints) constructor_arguments 
          | S: ('bs, 'b, 'ms, 'm, 'self, 'hyps, 'constraints)
          constructor_arguments -> ('self -> 'bs, 'self -> 'b, 'self -> 'ms,
          'self -> 'm, 'self, 'hyps, 'constraints) constructor_arguments 
          | C:
          (('self, 'hyps, 'constraints) ContextualConversion.t ->
             ('a, 'hyps, 'constraints) ContextualConversion.t)
          * ('bs, 'b, 'ms, 'm, 'self, 'hyps, 'constraints)
          constructor_arguments -> ('a -> 'bs, 'a -> 'b, 'a -> 'ms, 'a -> 'm,
          'self, 'hyps, 'constraints) constructor_arguments 
        type ('t, 'h, 'c) constructor =
          | K: name * doc * ('build_stateful_t, 'build_t, 'match_stateful_t,
          'match_t, 't, 'h, 'c) constructor_arguments * ('build_stateful_t,
          'build_t) build_t * ('match_stateful_t, 'match_t, 't) match_t ->
          ('t, 'h, 'c) constructor 
        type ('t, 'h, 'c) declaration =
          {
          ty: Conversion.ty_ast ;
          doc: doc ;
          pp: Format.formatter -> 't -> unit ;
          constructors: ('t, 'h, 'c) constructor list }
        type ('b, 'm, 't, 'h, 'c) compiled_constructor_arguments =
          | XN: (State.t -> (State.t * 't),
          State.t -> (State.t * term * extra_goals), 't, 'h, 'c)
          compiled_constructor_arguments 
          | XA: ('a, 'h, 'c) ContextualConversion.t * ('b, 'm, 't, 'h, 
          'c) compiled_constructor_arguments -> ('a -> 'b, 'a -> 'm, 
          't, 'h, 'c) compiled_constructor_arguments 
        type ('match_t, 't) compiled_match_t =
          ok:'match_t ->
            ko:(State.t -> (State.t * term * extra_goals)) ->
              't -> State.t -> (State.t * term * extra_goals)
        type ('t, 'h, 'c) compiled_constructor =
          | XK: ('build_t, 'matched_t, 't, 'h, 'c)
          compiled_constructor_arguments * 'build_t * ('matched_t, 't)
          compiled_match_t -> ('t, 'h, 'c) compiled_constructor 
        type ('t, 'h, 'c) compiled_adt =
          ('t, 'h, 'c) compiled_constructor Constants.Map.t
        let buildk ~mkConst  kname =
          function | [] -> mkConst kname | x::xs -> mkApp kname x xs
        let rec readback_args : type a m t h c.
          look:(depth:int -> term -> term) ->
            Conversion.ty_ast ->
              depth:int ->
                h ->
                  c ->
                    State.t ->
                      extra_goals list ->
                        term ->
                          (a, m, t, h, c) compiled_constructor_arguments ->
                            a -> term list -> (State.t * t * extra_goals)
          =
          fun ~look ->
            fun ty ->
              fun ~depth ->
                fun hyps ->
                  fun constraints ->
                    fun state ->
                      fun extra ->
                        fun origin ->
                          fun args ->
                            fun convert ->
                              fun l ->
                                match (args, l) with
                                | (XN, []) ->
                                    let (state, x) = convert state in
                                    (state, x,
                                      (let open List in concat (rev extra)))
                                | (XN, _) ->
                                    raise
                                      (Conversion.TypeErr (ty, depth, origin))
                                | (XA _, []) -> assert false
                                | (XA (d, rest), x::xs) ->
                                    let (state, x, gls) =
                                      d.readback ~depth hyps constraints
                                        state x in
                                    readback_args ~look ty ~depth hyps
                                      constraints state (gls :: extra) origin
                                      rest (convert x) xs
        and readback : type t h c.
          mkinterval:(int -> int -> int -> term list) ->
            look:(depth:int -> term -> term) ->
              alloc:(?name:string -> State.t -> (State.t * 'uk)) ->
                mkUnifVar:('uk -> args:term list -> State.t -> term) ->
                  Conversion.ty_ast ->
                    (t, h, c) compiled_adt ->
                      depth:int ->
                        h ->
                          c -> State.t -> term -> (State.t * t * extra_goals)
          =
          fun ~mkinterval ->
            fun ~look ->
              fun ~alloc ->
                fun ~mkUnifVar ->
                  fun ty ->
                    fun adt ->
                      fun ~depth ->
                        fun hyps ->
                          fun constraints ->
                            fun state ->
                              fun t ->
                                try
                                  match look ~depth t with
                                  | Const c ->
                                      let XK (args, read, _) =
                                        Constants.Map.find c adt in
                                      readback_args ~look ty ~depth hyps
                                        constraints state [] t args read []
                                  | App (c, x, xs) ->
                                      let XK (args, read, _) =
                                        Constants.Map.find c adt in
                                      readback_args ~look ty ~depth hyps
                                        constraints state [] t args read (x
                                        :: xs)
                                  | UVar _|AppUVar _ ->
                                      let XK (args, read, _) =
                                        Constants.Map.find
                                          Global_symbols.uvarc adt in
                                      readback_args ~look ty ~depth hyps
                                        constraints state [] t args read 
                                        [t]
                                  | Discard ->
                                      let XK (args, read, _) =
                                        Constants.Map.find
                                          Global_symbols.uvarc adt in
                                      let (state, k) = alloc state in
                                      readback_args ~look ty ~depth hyps
                                        constraints state [] t args read
                                        [mkUnifVar k
                                           ~args:(mkinterval 0 depth 0) state]
                                  | _ ->
                                      raise
                                        (Conversion.TypeErr (ty, depth, t))
                                with
                                | Not_found ->
                                    raise (Conversion.TypeErr (ty, depth, t))
        and adt_embed_args : type m a t h c.
          mkConst:(int -> term) ->
            Conversion.ty_ast ->
              (t, h, c) compiled_adt ->
                constant ->
                  depth:int ->
                    h ->
                      c ->
                        (a, m, t, h, c) compiled_constructor_arguments ->
                          (State.t -> (State.t * term * extra_goals)) list ->
                            m
          =
          fun ~mkConst ->
            fun ty ->
              fun adt ->
                fun kname ->
                  fun ~depth ->
                    fun hyps ->
                      fun constraints ->
                        fun args ->
                          fun acc ->
                            match args with
                            | XN ->
                                (fun state ->
                                   let (state, ts, gls) =
                                     List.fold_left
                                       (fun (state, acc, gls) ->
                                          fun f ->
                                            let (state, t, goals) = f state in
                                            (state, (t :: acc), (goals ::
                                              gls))) (state, [], []) acc in
                                   (state, (buildk ~mkConst kname ts),
                                     (let open List in flatten gls)))
                            | XA (d, args) ->
                                (fun x ->
                                   adt_embed_args ~mkConst ty adt kname
                                     ~depth hyps constraints args
                                     ((fun state ->
                                         d.embed ~depth hyps constraints
                                           state x) :: acc))
        and embed : type a h c.
          mkConst:(int -> term) ->
            Conversion.ty_ast ->
              (Format.formatter -> a -> unit) ->
                (a, h, c) compiled_adt ->
                  depth:int ->
                    h -> c -> State.t -> a -> (State.t * term * extra_goals)
          =
          fun ~mkConst ->
            fun ty ->
              fun pp ->
                fun adt ->
                  let bindings = Constants.Map.bindings adt in
                  fun ~depth ->
                    fun hyps ->
                      fun constraints ->
                        fun state ->
                          fun t ->
                            let rec aux l state =
                              match l with
                              | [] ->
                                  type_error
                                    ("Pattern matching failure embedding: " ^
                                       ((Conversion.show_ty_ast ty) ^
                                          (Format.asprintf ": %a" pp t)))
                              | (kname, XK (args, _, matcher))::rest ->
                                  let ok =
                                    adt_embed_args ~mkConst ty adt kname
                                      ~depth hyps constraints args [] in
                                  matcher ~ok ~ko:(aux rest) t state in
                            aux bindings state
        let rec compile_arguments : type b bs m ms t h c.
          (bs, b, ms, m, t, h, c) constructor_arguments ->
            (t, h, c) ContextualConversion.t ->
              (bs, ms, t, h, c) compiled_constructor_arguments
          =
          fun arg ->
            fun self ->
              match arg with
              | N -> XN
              | A (d, rest) ->
                  XA
                    ((ContextualConversion.(!>) d),
                      (compile_arguments rest self))
              | CA (d, rest) -> XA (d, (compile_arguments rest self))
              | S rest -> XA (self, (compile_arguments rest self))
              | C (fs, rest) -> XA ((fs self), (compile_arguments rest self))
        let rec compile_builder_aux : type bs b m ms t h c.
          (bs, b, ms, m, t, h, c) constructor_arguments -> b -> bs =
          fun args ->
            fun f ->
              match args with
              | N -> (fun state -> (state, f))
              | A (_, rest) -> (fun a -> compile_builder_aux rest (f a))
              | CA (_, rest) -> (fun a -> compile_builder_aux rest (f a))
              | S rest -> (fun a -> compile_builder_aux rest (f a))
              | C (_, rest) -> (fun a -> compile_builder_aux rest (f a))
        let compile_builder : type bs b m ms t h c.
          (bs, b, ms, m, t, h, c) constructor_arguments ->
            (bs, b) build_t -> bs
          = fun a -> function | B f -> compile_builder_aux a f | BS f -> f
        let rec compile_matcher_ok : type bs b m ms t h c.
          (bs, b, ms, m, t, h, c) constructor_arguments ->
            ms -> extra_goals ref -> State.t ref -> m
          =
          fun args ->
            fun f ->
              fun gls ->
                fun state ->
                  match args with
                  | N ->
                      let (state', t, gls') = f (!state) in
                      (state := state'; gls := gls'; t)
                  | A (_, rest) ->
                      (fun a -> compile_matcher_ok rest (f a) gls state)
                  | CA (_, rest) ->
                      (fun a -> compile_matcher_ok rest (f a) gls state)
                  | S rest ->
                      (fun a -> compile_matcher_ok rest (f a) gls state)
                  | C (_, rest) ->
                      (fun a -> compile_matcher_ok rest (f a) gls state)
        let compile_matcher_ko f gls state () =
          let (state', t, gls') = f (!state) in
          state := state'; gls := gls'; t
        let compile_matcher : type bs b m ms t h c.
          (bs, b, ms, m, t, h, c) constructor_arguments ->
            (ms, m, t) match_t -> (ms, t) compiled_match_t
          =
          fun a ->
            function
            | M f ->
                (fun ~ok ->
                   fun ~ko ->
                     fun t ->
                       fun state ->
                         let state = ref state in
                         let gls = ref [] in
                         ((!state),
                           (f ~ok:(compile_matcher_ok a ok gls state)
                              ~ko:(compile_matcher_ko ko gls state) t),
                           (!gls)))
            | MS f -> f
        let rec tyargs_of_args : type a b c d e.
          string ->
            (a, b, c, d, e) compiled_constructor_arguments ->
              (bool * string * string) list
          =
          fun self ->
            function
            | XN -> [(false, self, "")]
            | XA ({ ty }, rest) -> (false, (Conversion.show_ty_ast ty), "")
                :: (tyargs_of_args self rest)
        let compile_constructors ty self self_name l =
          let names =
            List.fold_right (fun (K (name, _, _, _, _)) -> StrSet.add name) l
              StrSet.empty in
          if (StrSet.cardinal names) <> (List.length l)
          then
            anomaly
              ("Duplicate constructors name in ADT: " ^
                 (Conversion.show_ty_ast ty));
          List.fold_left
            (fun (acc, sacc) ->
               fun (K (name, _, a, b, m)) ->
                 let c = Global_symbols.declare_global_symbol name in
                 let args = compile_arguments a self in
                 ((Constants.Map.add c
                     (XK (args, (compile_builder a b), (compile_matcher a m)))
                     acc),
                   (StrMap.add name (tyargs_of_args self_name args) sacc)))
            (Constants.Map.empty, StrMap.empty) l
        let document_constructor fmt name doc argsdoc =
          Fmt.fprintf fmt "@[<hov2>type %s@[<hov>%a.%s@]@]@\n" name
            pp_ty_args argsdoc (if doc = "" then "" else " % " ^ doc)
        let document_kind fmt =
          function
          | Conversion.TyApp (s, _, l) ->
              let n = (List.length l) + 2 in
              let l = Array.init n (fun _ -> "type") in
              Fmt.fprintf fmt "@[<hov 2>kind %s %s.@]@\n" s
                (String.concat " -> " (Array.to_list l))
          | Conversion.TyName s ->
              Fmt.fprintf fmt "@[<hov 2>kind %s type.@]@\n" s
        let document_adt doc ty ks cks fmt () =
          if doc <> ""
          then (pp_comment fmt ("% " ^ doc); Fmt.fprintf fmt "@\n");
          document_kind fmt ty;
          List.iter
            (fun (K (name, doc, _, _, _)) ->
               if name <> "uvar"
               then
                 let argsdoc = StrMap.find name cks in
                 document_constructor fmt name doc argsdoc) ks
        let adt ~mkinterval  ~look  ~mkConst  ~alloc  ~mkUnifVar 
          { ty; constructors; doc; pp } =
          let readback_ref =
            ref
              (fun ~depth -> fun _ -> fun _ -> fun _ -> fun _ -> assert false) in
          let embed_ref =
            ref
              (fun ~depth -> fun _ -> fun _ -> fun _ -> fun _ -> assert false) in
          let sconstructors_ref = ref StrMap.empty in
          let self =
            {
              ContextualConversion.ty = ty;
              pp;
              pp_doc =
                (fun fmt ->
                   fun () ->
                     document_adt doc ty constructors (!sconstructors_ref)
                       fmt ());
              readback =
                (fun ~depth ->
                   fun hyps ->
                     fun constraints ->
                       fun state ->
                         fun term ->
                           (!readback_ref) ~depth hyps constraints state term);
              embed =
                (fun ~depth ->
                   fun hyps ->
                     fun constraints ->
                       fun state ->
                         fun term ->
                           (!embed_ref) ~depth hyps constraints state term)
            } in
          let (cconstructors, sconstructors) =
            compile_constructors ty self (Conversion.show_ty_ast ty)
              constructors in
          sconstructors_ref := sconstructors;
          readback_ref :=
            (readback ~mkinterval ~look ~alloc ~mkUnifVar ty cconstructors);
          embed_ref := (embed ~mkConst ty pp cconstructors);
          self
      end
    type declaration =
      | MLCode of t * doc_spec 
      | MLData: 'a Conversion.t -> declaration 
      | MLDataC: ('a, 'h, 'c) ContextualConversion.t -> declaration 
      | LPDoc of string 
      | LPCode of string 
    let pp_tab_arg i sep fmt (dir, ty, doc) =
      let dir = if dir then "i" else "o" in
      if i = 0 then Fmt.pp_set_tab fmt () else ();
      Fmt.fprintf fmt "%s:%s%s" dir ty sep;
      if i = 0 then Fmt.pp_set_tab fmt () else Fmt.pp_print_tab fmt ();
      if doc <> "" then Fmt.fprintf fmt " %% %s" doc;
      Fmt.pp_print_tab fmt ()
    let pp_tab_args fmt l =
      let n = (List.length l) - 1 in
      Fmt.pp_open_tbox fmt ();
      List.iteri
        (fun i ->
           fun x ->
             let sep = if i = n then "." else "," in pp_tab_arg i sep fmt x)
        l;
      Fmt.pp_close_tbox fmt ()
    let pp_arg sep fmt (dir, ty, doc) =
      let dir = if dir then "i" else "o" in
      Fmt.fprintf fmt "%s:%s%s" dir ty sep
    let pp_args = pplist (pp_arg "") ", " ~pplastelem:(pp_arg "")
    let pp_pred fmt docspec name doc_pred args =
      let args = List.rev args in
      match docspec with
      | DocNext ->
          Fmt.fprintf fmt "@[<v 2>external pred %s %% %s@;%a@]@." name
            doc_pred pp_tab_args args
      | DocAbove ->
          let doc =
            "[" ^
              ((String.concat " " (name ::
                  (List.map (fun (_, _, x) -> x) args)))
                 ^ ("] " ^ doc_pred)) in
          Fmt.fprintf fmt "@[<v>%% %a@.external pred %s @[<hov>%a.@]@]@.@."
            pp_comment doc name pp_args args
    let pp_variadictype fmt name doc_pred ty args =
      let parens s = if String.contains s ' ' then "(" ^ (s ^ ")") else s in
      let args =
        List.rev ((false, ("variadic " ^ ((parens ty) ^ " prop")), "") ::
          args) in
      let doc =
        "[" ^
          ((String.concat " " (name :: (List.map (fun (_, _, x) -> x) args)))
             ^ ("...] " ^ doc_pred)) in
      Fmt.fprintf fmt "@[<v>%% %a@.external type %s@[<hov>%a.@]@]@.@."
        pp_comment doc name pp_ty_args args
    let document_pred fmt docspec name ffi =
      let rec doc : type i o h c.
        (bool * string * string) list -> (i, o, h, c) ffi -> unit =
        fun args ->
          function
          | In ({ Conversion.ty = ty }, s, ffi) ->
              doc ((true, (Conversion.show_ty_ast ty), s) :: args) ffi
          | Out ({ Conversion.ty = ty }, s, ffi) ->
              doc ((false, (Conversion.show_ty_ast ty), s) :: args) ffi
          | InOut ({ Conversion.ty = ty }, s, ffi) ->
              doc ((false, (Conversion.show_ty_ast ty), s) :: args) ffi
          | CIn ({ ContextualConversion.ty = ty }, s, ffi) ->
              doc ((true, (Conversion.show_ty_ast ty), s) :: args) ffi
          | COut ({ ContextualConversion.ty = ty }, s, ffi) ->
              doc ((false, (Conversion.show_ty_ast ty), s) :: args) ffi
          | CInOut ({ ContextualConversion.ty = ty }, s, ffi) ->
              doc ((false, (Conversion.show_ty_ast ty), s) :: args) ffi
          | Read (_, s) -> pp_pred fmt docspec name s args
          | Easy s -> pp_pred fmt docspec name s args
          | Full (_, s) -> pp_pred fmt docspec name s args
          | VariadicIn (_, { ContextualConversion.ty = ty }, s) ->
              pp_variadictype fmt name s (Conversion.show_ty_ast ty) args
          | VariadicOut (_, { ContextualConversion.ty = ty }, s) ->
              pp_variadictype fmt name s (Conversion.show_ty_ast ty) args
          | VariadicInOut (_, { ContextualConversion.ty = ty }, s) ->
              pp_variadictype fmt name s (Conversion.show_ty_ast ty) args in
      doc [] ffi
    let document fmt l =
      let omargin = Fmt.pp_get_margin fmt () in
      Fmt.pp_set_margin fmt 75;
      Fmt.fprintf fmt "@[<v>";
      Fmt.fprintf fmt "@\n@\n";
      List.iter
        (function
         | MLCode (Pred (name, ffi, _), docspec) ->
             document_pred fmt docspec name ffi
         | MLData { pp_doc } -> Fmt.fprintf fmt "%a@\n" pp_doc ()
         | MLDataC { pp_doc } -> Fmt.fprintf fmt "%a@\n" pp_doc ()
         | LPCode s -> (Fmt.fprintf fmt "%s" s; Fmt.fprintf fmt "@\n@\n")
         | LPDoc s -> (pp_comment fmt ("% " ^ s); Fmt.fprintf fmt "@\n@\n"))
        l;
      Fmt.fprintf fmt "@\n@\n";
      Fmt.fprintf fmt "@]@.";
      Fmt.pp_set_margin fmt omargin
    type builtin_table = (int, t) Hashtbl.t
  end
module Query =
  struct
    type name = string
    type _ arguments =
      | N: unit arguments 
      | D: 'a Conversion.t * 'a * 'x arguments -> 'x arguments 
      | Q: 'a Conversion.t * name * 'x arguments -> ('a * 'x) arguments 
    type 'x t =
      | Query of {
      predicate: constant ;
      arguments: 'x arguments } 
  end
type symbol_table =
  {
  c2s: (constant, string) Hashtbl.t ;
  c2t: (constant, term) Hashtbl.t ;
  mutable frozen_constants: int }[@@deriving show]
let rec pp_symbol_table :
  Ppx_deriving_runtime_proxy.Format.formatter ->
    symbol_table -> Ppx_deriving_runtime_proxy.unit
  =
  let __4 () = Hashtbl.pp
  and __3 () = pp_term
  and __2 () = pp_constant
  and __1 () = Hashtbl.pp
  and __0 () = pp_constant in
  ((let open! Ppx_deriving_runtime_proxy in
      fun fmt ->
        fun x ->
          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
          (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "Data.c2s";
             ((__1 ()) (fun fmt -> (__0 ()) fmt)
                (fun fmt -> Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") fmt)
               x.c2s;
             Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
            Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
            Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "c2t";
            ((__4 ()) (fun fmt -> (__2 ()) fmt) (fun fmt -> (__3 ()) fmt) fmt)
              x.c2t;
            Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
           Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
           Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
             "frozen_constants";
           (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.frozen_constants;
           Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
          Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
    [@ocaml.warning "-A"])
and show_symbol_table : symbol_table -> Ppx_deriving_runtime_proxy.string =
  fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_symbol_table x
[@@ocaml.warning "-32"]
type 'a executable =
  {
  compiled_program: prolog_prog ;
  chr: CHR.t ;
  initial_depth: int ;
  initial_goal: term ;
  initial_runtime_state: State.t ;
  symbol_table: symbol_table ;
  builtins: BuiltInPredicate.builtin_table ;
  assignments: term Util.StrMap.t ;
  query_arguments: 'a Query.arguments }
type pp_ctx =
  {
  uv_names: (string Util.PtrMap.t * int) ref ;
  table: symbol_table }
type 'a solution =
  {
  assignments: term StrMap.t ;
  constraints: constraints ;
  state: State.t ;
  output: 'a ;
  pp_ctx: pp_ctx }
type 'a outcome =
  | Success of 'a solution 
  | Failure 
  | NoMoreSteps 

