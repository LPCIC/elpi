(*5985c493149e486491278f47254411fe src/ast.ml *)
#1 "src/ast.ml"
open Util
module Func =
  struct
    module Self =
      struct
        type t = string
        let compare = String.compare
        let from_string =
          let h = Hashtbl.create 37 in
          let rec aux =
            function
            | "nil" -> aux "[]"
            | "cons" -> aux "::"
            | "&" -> aux ","
            | x ->
                (try Hashtbl.find h x
                 with | Not_found -> (Hashtbl.add h x x; x)) in
          aux
        let pp fmt s = Format.fprintf fmt "%s" s
        let show x = x
        let equal x y = (x == y) || (x = y)
        let truef = from_string "true"
        let andf = from_string ","
        let orf = from_string ";"
        let implf = from_string "=>"
        let rimplf = from_string ":-"
        let cutf = from_string "!"
        let pif = from_string "pi"
        let sigmaf = from_string "sigma"
        let eqf = from_string "="
        let isf = from_string "is"
        let consf = from_string "::"
        let nilf = from_string "[]"
        let arrowf = from_string "->"
        let sequentf = from_string "?-"
        let ctypef = from_string "ctype"
        let dummyname = from_string "%dummy"
        let spillf = from_string "%spill"
      end
    include Self
    module Map = (Map.Make)(Self)
  end
module Term =
  struct
    type t =
      | Const of Func.t 
      | App of t * t list 
      | Lam of Func.t * t 
      | CData of CData.t 
      | Quoted of quote 
    and quote = {
      data: string ;
      loc: Loc.t ;
      kind: string option }[@@deriving show]
    let rec pp :
      Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
      =
      let __6 () = pp_quote
      and __5 () = CData.pp
      and __4 () = pp
      and __3 () = Func.pp
      and __2 () = pp
      and __1 () = pp
      and __0 () = Func.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Const a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Term.Const@ ";
                 ((__0 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | App (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Term.App (@,";
                 (((__1 ()) fmt) a0;
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
                                ((__2 ()) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Lam (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Term.Lam (@,";
                 (((__3 ()) fmt) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__4 ()) fmt) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | CData a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Term.CData@ ";
                 ((__5 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Quoted a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Term.Quoted@ ";
                 ((__6 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
        [@ocaml.warning "-A"])
    and show : t -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp x[@@ocaml.warning
                                                               "-32"]
    and pp_quote :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        quote -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "Ast.Term.data";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x.data;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "loc";
                ((__0 ()) fmt) x.loc;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "kind";
               ((function
                 | None ->
                     Ppx_deriving_runtime_proxy.Format.pp_print_string fmt "None"
                 | Some x ->
                     (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                        "(Some ";
                      (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x;
                      Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                 x.kind;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_quote : quote -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_quote x[@@ocaml.warning
                                                                    "-32"]
    let mkC x = CData x
    let mkLam x t = Lam ((Func.from_string x), t)
    let mkNil = Const Func.nilf
    let mkQuoted loc s =
      let strip n m loc =
        {
          loc with
          Loc.source_start = (loc.Loc.source_start + n);
          source_stop = (loc.Loc.source_stop - m);
          line_starts_at = (loc.Loc.line_starts_at - m)
        } in
      let loc = strip 2 2 loc in
      let rec find_data i =
        match s.[i] with
        | '{' -> find_data (i + 1)
        | ':' ->
            let rec find_space i =
              match s.[i] with
              | ' ' -> i
              | '\n' -> i
              | _ -> find_space (i + 1) in
            let space_after = (find_space 0) - 1 in
            let kind = String.sub s (i + 1) space_after in
            let data =
              String.sub s ((i + space_after) + 2)
                (((((String.length s) - i) - i) - space_after) - 2) in
            {
              loc = (strip ((i + space_after) + 2) i loc);
              data;
              kind = (Some kind)
            }
        | _ ->
            {
              loc = (strip i i loc);
              data = (String.sub s i (((String.length s) - i) - i));
              kind = None
            } in
      Quoted (find_data 0)
    let mkSeq l =
      let rec aux =
        function
        | [] -> assert false
        | e::[] -> e
        | hd::tl -> App ((Const Func.consf), [hd; aux tl]) in
      aux l
    let mkIs x f = App ((Const Func.isf), [x; f])
    exception NotInProlog of Loc.t * string 
    let mkApp loc =
      function
      | (App _|Const _|Quoted _ as c)::[] -> c
      | (App (c, l1))::l2 -> App (c, (l1 @ l2))
      | (Const _|Quoted _ as c)::l2 -> App (c, l2)
      | [] -> raise (NotInProlog (loc, "empty application"))
      | x::_ -> raise (NotInProlog (loc, ("application head: " ^ (show x))))
    let fresh_uv_names = ref (-1)
    let mkFreshUVar () =
      incr fresh_uv_names;
      Const (Func.from_string ("_" ^ (string_of_int (!fresh_uv_names))))
    let fresh_names = ref (-1)
    let mkFreshName () =
      incr fresh_names;
      Const (Func.from_string ("__" ^ (string_of_int (!fresh_names))))
    let mkCon c = Const (Func.from_string c)
  end
module Clause =
  struct
    type attribute =
      | Name of string 
      | After of string 
      | Before of string 
      | If of string [@@deriving show]
    let rec pp_attribute :
              Ppx_deriving_runtime_proxy.Format.formatter ->
                attribute -> Ppx_deriving_runtime_proxy.unit
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Name a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Clause.Name@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | After a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Clause.After@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Before a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Clause.Before@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | If a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Clause.If@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])
    and show_attribute : attribute -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_attribute x
    [@@ocaml.warning "-32"]
    type ('term, 'attributes) t =
      {
      loc: Loc.t ;
      attributes: 'attributes ;
      body: 'term }[@@deriving show]
    let rec pp :
      'term 'attributes .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'term -> Ppx_deriving_runtime_proxy.unit)
          ->
          (Ppx_deriving_runtime_proxy.Format.formatter ->
             'attributes -> Ppx_deriving_runtime_proxy.unit)
            ->
            Ppx_deriving_runtime_proxy.Format.formatter ->
              ('term, 'attributes) t -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_term ->
            fun poly_attributes ->
              fun fmt ->
                fun x ->
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                  (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "Ast.Clause.loc";
                     ((__0 ()) fmt) x.loc;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "attributes";
                    (poly_attributes fmt) x.attributes;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "body";
                   (poly_term fmt) x.body;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'term 'attributes .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'term -> Ppx_deriving_runtime_proxy.unit)
          ->
          (Ppx_deriving_runtime_proxy.Format.formatter ->
             'attributes -> Ppx_deriving_runtime_proxy.unit)
            -> ('term, 'attributes) t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_term ->
        fun poly_attributes ->
          fun x ->
            Ppx_deriving_runtime_proxy.Format.asprintf "%a"
              ((pp poly_term) poly_attributes) x[@@ocaml.warning "-32"]
  end
module Chr =
  struct
    type attribute =
      | Name of string 
      | If of string [@@deriving show]
    let rec pp_attribute :
              Ppx_deriving_runtime_proxy.Format.formatter ->
                attribute -> Ppx_deriving_runtime_proxy.unit
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Name a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Chr.Name@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | If a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt "(@[<2>Ast.Chr.If@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])
    and show_attribute : attribute -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_attribute x
    [@@ocaml.warning "-32"]
    type sequent = {
      eigen: Term.t ;
      context: Term.t ;
      conclusion: Term.t }
    and 'attribute t =
      {
      to_match: sequent list ;
      to_remove: sequent list ;
      guard: Term.t option ;
      new_goal: sequent option ;
      attributes: 'attribute ;
      loc: Loc.t }[@@deriving (show, create)]
    let rec pp_sequent :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        sequent -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = Term.pp
      and __1 () = Term.pp
      and __0 () = Term.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "Ast.Chr.eigen";
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
    and pp :
      'attribute .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'attribute -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            'attribute t -> Ppx_deriving_runtime_proxy.unit
      =
      let __4 () = Loc.pp
      and __3 () = pp_sequent
      and __2 () = Term.pp
      and __1 () = pp_sequent
      and __0 () = pp_sequent in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_attribute ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                ((((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                        "Ast.Chr.to_match";
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
                      "guard";
                    ((function
                      | None ->
                          Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                            "None"
                      | Some x ->
                          (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                             "(Some ";
                           ((__2 ()) fmt) x;
                           Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                             ")"))) x.guard;
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
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                    "attributes";
                  (poly_attribute fmt) x.attributes;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "loc";
                 ((__4 ()) fmt) x.loc;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'attribute .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'attribute -> Ppx_deriving_runtime_proxy.unit)
          -> 'attribute t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_attribute ->
        fun x ->
          Ppx_deriving_runtime_proxy.Format.asprintf "%a" (pp poly_attribute) x
    [@@ocaml.warning "-32"]
    let create_sequent =
      ((let open! Ppx_deriving_runtime_proxy in
          fun ~eigen ->
            fun ~context ->
              fun ~conclusion -> fun () -> { eigen; context; conclusion })
      [@ocaml.warning "-A"])
    and create =
      ((let open! Ppx_deriving_runtime_proxy in
          fun ?(to_match= []) ->
            fun ?(to_remove= []) ->
              fun ?guard ->
                fun ?new_goal ->
                  fun ~attributes ->
                    fun ~loc ->
                      fun () ->
                        {
                          to_match;
                          to_remove;
                          guard;
                          new_goal;
                          attributes;
                          loc
                        })
      [@ocaml.warning "-A"])
  end
module Macro =
  struct
    type ('name, 'term) t = {
      loc: Loc.t ;
      name: 'name ;
      body: 'term }[@@deriving show]
    let rec pp :
      'name 'term .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'name -> Ppx_deriving_runtime_proxy.unit)
          ->
          (Ppx_deriving_runtime_proxy.Format.formatter ->
             'term -> Ppx_deriving_runtime_proxy.unit)
            ->
            Ppx_deriving_runtime_proxy.Format.formatter ->
              ('name, 'term) t -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_name ->
            fun poly_term ->
              fun fmt ->
                fun x ->
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                  (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                       "Ast.Macro.loc";
                     ((__0 ()) fmt) x.loc;
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "name";
                    (poly_name fmt) x.name;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "body";
                   (poly_term fmt) x.body;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'name 'term .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'name -> Ppx_deriving_runtime_proxy.unit)
          ->
          (Ppx_deriving_runtime_proxy.Format.formatter ->
             'term -> Ppx_deriving_runtime_proxy.unit)
            -> ('name, 'term) t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_name ->
        fun poly_term ->
          fun x ->
            Ppx_deriving_runtime_proxy.Format.asprintf "%a"
              ((pp poly_name) poly_term) x[@@ocaml.warning "-32"]
  end
module Type =
  struct
    type attribute =
      | External 
      | Index of int list [@@deriving show]
    let rec pp_attribute :
              Ppx_deriving_runtime_proxy.Format.formatter ->
                attribute -> Ppx_deriving_runtime_proxy.unit
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | External ->
                Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                  "Ast.Type.External"
            | Index a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Type.Index@ ";
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
    and show_attribute : attribute -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_attribute x
    [@@ocaml.warning "-32"]
    type 'attribute t =
      {
      loc: Loc.t ;
      attributes: 'attribute ;
      name: Func.t ;
      ty: Term.t }[@@deriving show]
    let rec pp :
      'attribute .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'attribute -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            'attribute t -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = Term.pp
      and __1 () = Func.pp
      and __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_attribute ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                ((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "Ast.Type.loc";
                    ((__0 ()) fmt) x.loc;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                     "attributes";
                   (poly_attribute fmt) x.attributes;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "name";
                  ((__1 ()) fmt) x.name;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "ty";
                 ((__2 ()) fmt) x.ty;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'attribute .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'attribute -> Ppx_deriving_runtime_proxy.unit)
          -> 'attribute t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_attribute ->
        fun x ->
          Ppx_deriving_runtime_proxy.Format.asprintf "%a" (pp poly_attribute) x
    [@@ocaml.warning "-32"]
  end
module Mode =
  struct
    type 'name t = {
      name: 'name ;
      args: bool list ;
      loc: Loc.t }[@@deriving show]
    let rec pp :
      'name .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'name -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            'name t -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_name ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                     "Ast.Mode.name";
                   (poly_name fmt) x.name;
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
                                (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%B")
                                  x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                    x.args;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "loc";
                 ((__0 ()) fmt) x.loc;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'name .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'name -> Ppx_deriving_runtime_proxy.unit)
          -> 'name t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_name ->
        fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" (pp poly_name) x
    [@@ocaml.warning "-32"]
  end
module TypeAbbreviation =
  struct
    type 'name t = {
      name: 'name ;
      value: Term.t ;
      nparams: int ;
      loc: Loc.t }[@@deriving show]
    let rec pp :
      'name .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'name -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            'name t -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () = Loc.pp
      and __0 () = Term.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_name ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                ((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                      "Ast.TypeAbbreviation.name";
                    (poly_name fmt) x.name;
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "value";
                   ((__0 ()) fmt) x.value;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                    "nparams";
                  (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%d") x.nparams;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "loc";
                 ((__1 ()) fmt) x.loc;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show :
      'name .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'name -> Ppx_deriving_runtime_proxy.unit)
          -> 'name t -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_name ->
        fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" (pp poly_name) x
    [@@ocaml.warning "-32"]
  end
module Program =
  struct
    type decl =
      | Begin of Loc.t 
      | Namespace of Loc.t * Func.t 
      | Constraint of Loc.t * Func.t list 
      | Shorten of Loc.t * Func.t * Func.t 
      | End of Loc.t 
      | Accumulated of Loc.t * (Digest.t * decl list) 
      | Clause of (Term.t, Clause.attribute list) Clause.t 
      | Local of Func.t 
      | Mode of Func.t Mode.t list 
      | Chr of Chr.attribute list Chr.t 
      | Macro of (Func.t, Term.t) Macro.t 
      | Type of Type.attribute list Type.t 
      | TypeAbbreviation of Func.t TypeAbbreviation.t [@@deriving show]
    let rec pp_decl :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        decl -> Ppx_deriving_runtime_proxy.unit
      =
      let __26 () = TypeAbbreviation.pp
      and __25 () = Func.pp
      and __24 () = Type.pp
      and __23 () = Type.pp_attribute
      and __22 () = Macro.pp
      and __21 () = Term.pp
      and __20 () = Func.pp
      and __19 () = Chr.pp
      and __18 () = Chr.pp_attribute
      and __17 () = Mode.pp
      and __16 () = Func.pp
      and __15 () = Func.pp
      and __14 () = Clause.pp
      and __13 () = Clause.pp_attribute
      and __12 () = Term.pp
      and __11 () = pp_decl
      and __10 () = Digest.pp
      and __9 () = Loc.pp
      and __8 () = Loc.pp
      and __7 () = Func.pp
      and __6 () = Func.pp
      and __5 () = Loc.pp
      and __4 () = Func.pp
      and __3 () = Loc.pp
      and __2 () = Func.pp
      and __1 () = Loc.pp
      and __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Begin a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Begin@ ";
                 ((__0 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Namespace (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Namespace (@,";
                 (((__1 ()) fmt) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__2 ()) fmt) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Constraint (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Constraint (@,";
                 (((__3 ()) fmt) a0;
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
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Shorten (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Shorten (@,";
                 ((((__5 ()) fmt) a0;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                   ((__6 ()) fmt) a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__7 ()) fmt) a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | End a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.End@ ";
                 ((__8 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Accumulated (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Accumulated (@,";
                 (((__9 ()) fmt) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((fun (a0, a1) ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "(@[";
                      (((__10 ()) fmt) a0;
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                       ((fun x ->
                           Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                           ignore
                             (List.fold_left
                                (fun sep ->
                                   fun x ->
                                     if sep
                                     then
                                       Ppx_deriving_runtime_proxy.Format.fprintf
                                         fmt ";@ ";
                                     ((__11 ()) fmt) x;
                                     true) false x);
                           Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                         a1);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Clause a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Clause@ ";
                 ((__14 ()) (fun fmt -> (__12 ()) fmt)
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
                                   ((__13 ()) fmt) x;
                                   true) false x);
                         Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]") fmt)
                   a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Local a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Local@ ";
                 ((__15 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Mode a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Mode@ ";
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
                               ((__17 ()) (fun fmt -> (__16 ()) fmt) fmt) x;
                               true) false x);
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Chr a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Chr@ ";
                 ((__19 ())
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
                                   ((__18 ()) fmt) x;
                                   true) false x);
                         Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]") fmt)
                   a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Macro a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Macro@ ";
                 ((__22 ()) (fun fmt -> (__20 ()) fmt)
                    (fun fmt -> (__21 ()) fmt) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Type a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.Type@ ";
                 ((__24 ())
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
                                   ((__23 ()) fmt) x;
                                   true) false x);
                         Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]") fmt)
                   a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | TypeAbbreviation a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Program.TypeAbbreviation@ ";
                 ((__26 ()) (fun fmt -> (__25 ()) fmt) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
        [@ocaml.warning "-A"])
    and show_decl : decl -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_decl x[@@ocaml.warning
                                                                    "-32"]
    let mkLocal x = Local (Func.from_string x)
    type t = decl list[@@deriving show]
    let rec pp :
      Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_decl in
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
    and show : t -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp x[@@ocaml.warning
                                                               "-32"]
  end
module Goal =
  struct
    type t = (Loc.t * Term.t)[@@deriving show]
    let rec pp :
      Ppx_deriving_runtime_proxy.Format.formatter -> t -> Ppx_deriving_runtime_proxy.unit
      =
      let __1 () = Term.pp
      and __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun (a0, a1) ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "(@[";
              (((__0 ()) fmt) a0;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
               ((__1 ()) fmt) a1);
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
        [@ocaml.warning "-A"])
    and show : t -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp x[@@ocaml.warning
                                                               "-32"]
  end
module Fmt = Format
let { CData.cin = in_float; isc = is_float; cout = out_float } as cfloat =
  let open CData in
    declare
      {
        data_name = "float";
        data_pp = (fun f -> fun x -> Fmt.fprintf f "%f" x);
        data_compare = Pervasives.compare;
        data_hash = Hashtbl.hash;
        data_hconsed = false
      }
let { CData.cin = in_int; isc = is_int; cout = out_int } as cint =
  let open CData in
    declare
      {
        data_name = "int";
        data_pp = (fun f -> fun x -> Fmt.fprintf f "%d" x);
        data_compare = Int.compare;
        data_hash = Hashtbl.hash;
        data_hconsed = false
      }
let { CData.cin = in_string; isc = is_string; cout = out_string } as cstring
  =
  let open CData in
    declare
      {
        data_name = "string";
        data_pp = (fun f -> fun x -> Fmt.fprintf f "%s" x);
        data_compare = String.compare;
        data_hash = Hashtbl.hash;
        data_hconsed = true
      }
let { CData.cin = in_loc; isc = is_loc; cout = out_loc } as cloc =
  let open CData in
    declare
      {
        data_name = "Loc.t";
        data_pp =
          (fun f ->
             fun x ->
               let bname = x.Loc.source_name in
               let line_no = x.Loc.line in
               Fmt.fprintf f "File %S, line %d:" bname line_no);
        data_compare = Pervasives.compare;
        data_hash = Hashtbl.hash;
        data_hconsed = false
      }
module Structured =
  struct
    type program =
      {
      macros: (Func.t, Term.t) Macro.t list ;
      types: tattribute Type.t list ;
      type_abbrevs: Func.t TypeAbbreviation.t list ;
      modes: Func.t Mode.t list ;
      body: block list }
    and block =
      | Locals of Func.t list * program 
      | Clauses of (Term.t, attribute) Clause.t list 
      | Namespace of Func.t * program 
      | Shorten of Func.t shorthand list * program 
      | Constraints of Func.t list * cattribute Chr.t list * program 
    and attribute =
      {
      insertion: insertion option ;
      id: string option ;
      ifexpr: string option }
    and insertion =
      | Before of string 
      | After of string 
    and cattribute = {
      cid: string ;
      cifexpr: string option }
    and tattribute =
      | External 
      | Indexed of int list 
    and 'a shorthand = {
      iloc: Loc.t ;
      full_name: 'a ;
      short_name: 'a }[@@deriving show]
    let rec pp_program :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        program -> Ppx_deriving_runtime_proxy.unit
      =
      let __9 () = pp_block
      and __8 () = Mode.pp
      and __7 () = Func.pp
      and __6 () = TypeAbbreviation.pp
      and __5 () = Func.pp
      and __4 () = Type.pp
      and __3 () = pp_tattribute
      and __2 () = Macro.pp
      and __1 () = Term.pp
      and __0 () = Func.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              (((((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                     "Ast.Structured.macros";
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
                                 ((__2 ()) (fun fmt -> (__0 ()) fmt)
                                    (fun fmt -> (__1 ()) fmt) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                     x.macros;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "types";
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
                                ((__4 ()) (fun fmt -> (__3 ()) fmt) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                    x.types;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "type_abbrevs";
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
                               ((__6 ()) (fun fmt -> (__5 ()) fmt) fmt) x;
                               true) false x);
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]"))
                   x.type_abbrevs;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "modes";
                ((fun x ->
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                    ignore
                      (List.fold_left
                         (fun sep ->
                            fun x ->
                              if sep
                              then
                                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                              ((__8 ()) (fun fmt -> (__7 ()) fmt) fmt) x;
                              true) false x);
                    Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) 
                  x.modes;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "body";
               ((fun x ->
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                   ignore
                     (List.fold_left
                        (fun sep ->
                           fun x ->
                             if sep
                             then
                               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                             ((__9 ()) fmt) x;
                             true) false x);
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) 
                 x.body;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_program : program -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_program x
    [@@ocaml.warning "-32"]
    and pp_block :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        block -> Ppx_deriving_runtime_proxy.unit
      =
      let __13 () = pp_program
      and __12 () = Chr.pp
      and __11 () = pp_cattribute
      and __10 () = Func.pp
      and __9 () = pp_program
      and __8 () = pp_shorthand
      and __7 () = Func.pp
      and __6 () = pp_program
      and __5 () = Func.pp
      and __4 () = Clause.pp
      and __3 () = pp_attribute
      and __2 () = Term.pp
      and __1 () = pp_program
      and __0 () = Func.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Locals (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Locals (@,";
                 (((fun x ->
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
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__1 ()) fmt) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Clauses a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Clauses@ ";
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
                               ((__4 ()) (fun fmt -> (__2 ()) fmt)
                                  (fun fmt -> (__3 ()) fmt) fmt) x;
                               true) false x);
                     Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | Namespace (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Namespace (@,";
                 (((__5 ()) fmt) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__6 ()) fmt) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Shorten (a0, a1) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Shorten (@,";
                 (((fun x ->
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                      ignore
                        (List.fold_left
                           (fun sep ->
                              fun x ->
                                if sep
                                then
                                  Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                    ";@ ";
                                ((__8 ()) (fun fmt -> (__7 ()) fmt) fmt) x;
                                true) false x);
                      Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a0;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__9 ()) fmt) a1);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]")
            | Constraints (a0, a1, a2) ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Constraints (@,";
                 ((((fun x ->
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>[";
                       ignore
                         (List.fold_left
                            (fun sep ->
                               fun x ->
                                 if sep
                                 then
                                   Ppx_deriving_runtime_proxy.Format.fprintf fmt
                                     ";@ ";
                                 ((__10 ()) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a0;
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
                                 ((__12 ()) (fun fmt -> (__11 ()) fmt) fmt) x;
                                 true) false x);
                       Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,]@]")) a1);
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ",@ ";
                  ((__13 ()) fmt) a2);
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@,))@]"))
        [@ocaml.warning "-A"])
    and show_block : block -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_block x[@@ocaml.warning
                                                                    "-32"]
    and pp_attribute :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        attribute -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_insertion in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "Ast.Structured.insertion";
                 ((function
                   | None ->
                       Ppx_deriving_runtime_proxy.Format.pp_print_string fmt "None"
                   | Some x ->
                       (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                          "(Some ";
                        ((__0 ()) fmt) x;
                        Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                   x.insertion;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "id";
                ((function
                  | None ->
                      Ppx_deriving_runtime_proxy.Format.pp_print_string fmt "None"
                  | Some x ->
                      (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                         "(Some ";
                       (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x;
                       Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                  x.id;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "ifexpr";
               ((function
                 | None ->
                     Ppx_deriving_runtime_proxy.Format.pp_print_string fmt "None"
                 | Some x ->
                     (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                        "(Some ";
                      (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x;
                      Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                 x.ifexpr;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_attribute : attribute -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_attribute x
    [@@ocaml.warning "-32"]
    and (pp_insertion :
          Ppx_deriving_runtime_proxy.Format.formatter ->
            insertion -> Ppx_deriving_runtime_proxy.unit)
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Before a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Before@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | After a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.After@ ";
                 (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
      [@ocaml.warning "-A"])
    and show_insertion : insertion -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_insertion x
    [@@ocaml.warning "-32"]
    and (pp_cattribute :
          Ppx_deriving_runtime_proxy.Format.formatter ->
            cattribute -> Ppx_deriving_runtime_proxy.unit)
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            fun x ->
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
              ((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                  "Ast.Structured.cid";
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x.cid;
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
               Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ " "cifexpr";
               ((function
                 | None ->
                     Ppx_deriving_runtime_proxy.Format.pp_print_string fmt "None"
                 | Some x ->
                     (Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                        "(Some ";
                      (Ppx_deriving_runtime_proxy.Format.fprintf fmt "%S") x;
                      Ppx_deriving_runtime_proxy.Format.pp_print_string fmt ")")))
                 x.cifexpr;
               Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
              Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
      [@ocaml.warning "-A"])
    and show_cattribute : cattribute -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_cattribute x
    [@@ocaml.warning "-32"]
    and (pp_tattribute :
          Ppx_deriving_runtime_proxy.Format.formatter ->
            tattribute -> Ppx_deriving_runtime_proxy.unit)
      =
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | External ->
                Ppx_deriving_runtime_proxy.Format.pp_print_string fmt
                  "Ast.Structured.External"
            | Indexed a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Ast.Structured.Indexed@ ";
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
    and show_tattribute : tattribute -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_tattribute x
    [@@ocaml.warning "-32"]
    and pp_shorthand :
      'a .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'a -> Ppx_deriving_runtime_proxy.unit)
          ->
          Ppx_deriving_runtime_proxy.Format.formatter ->
            'a shorthand -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = Loc.pp in
      ((let open! Ppx_deriving_runtime_proxy in
          fun poly_a ->
            fun fmt ->
              fun x ->
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[<2>{ ";
                (((Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                     "Ast.Structured.iloc";
                   ((__0 ()) fmt) x.iloc;
                   Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                    "full_name";
                  (poly_a fmt) x.full_name;
                  Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt ";@ ";
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@[%s =@ "
                   "short_name";
                 (poly_a fmt) x.short_name;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@]");
                Ppx_deriving_runtime_proxy.Format.fprintf fmt "@ }@]")
        [@ocaml.warning "-A"])
    and show_shorthand :
      'a .
        (Ppx_deriving_runtime_proxy.Format.formatter ->
           'a -> Ppx_deriving_runtime_proxy.unit)
          -> 'a shorthand -> Ppx_deriving_runtime_proxy.string
      =
      fun poly_a ->
        fun x ->
          Ppx_deriving_runtime_proxy.Format.asprintf "%a" (pp_shorthand poly_a) x
    [@@ocaml.warning "-32"]
  end

