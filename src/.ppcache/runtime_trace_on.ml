(*05283c3764b3dd6bbeeb85601a5ddc1e src/runtime_trace_on.ml --cookie elpi_trace="true"*)
#1 "src/runtime_trace_on.ml"
module Fmt = Format
module F = Ast.Func
open Util
open Data
type constraint_def =
  {
  cdepth: int ;
  prog: prolog_prog
    [@equal fun _ -> fun _ -> true][@printer
                                     fun fmt ->
                                       fun _ ->
                                         Fmt.fprintf fmt "<prolog_prog>"];
  context: clause_src list ;
  conclusion: term ;
  cgid: UUID.t [@trace ]}
type 'unification_def stuck_goal_kind +=  
  | Constraint of constraint_def 
let get_suspended_goal =
  function
  | Constraint { cdepth; conclusion; context;_} ->
      Some { context; goal = (cdepth, conclusion) }
  | _ -> None
module C :
  sig
    type t = Constants.t
    module Map = Constants.Map
    module Set = Constants.Set
    val show : ?table:symbol_table -> t -> string
    val pp : ?table:symbol_table -> Fmt.formatter -> t -> unit
    val mkConst : constant -> term
    val mkAppL : constant -> term list -> term
    val fresh_global_constant : unit -> (constant * term)
    val mkinterval : int -> int -> int -> term list
    val dummy : term
    val table : symbol_table Fork.local_ref
  end =
  struct
    type t = Constants.t
    let dummy = Data.dummy
    let table =
      Fork.new_local
        {
          c2s = (Hashtbl.create 37);
          c2t = (Hashtbl.create 37);
          frozen_constants = 0
        }
    let show ?(table= !table)  n =
      try Constants.Map.find n Global_symbols.table.c2s
      with
      | Not_found ->
          (try Hashtbl.find table.c2s n
           with
           | Not_found ->
               if n >= 0
               then "c" ^ (string_of_int n)
               else "SYMBOL" ^ (string_of_int n))
    let pp ?table  fmt n = Format.fprintf fmt "%s" (show ?table n)
    let mkConst x =
      try Hashtbl.find (!table).c2t x
      with
      | Not_found -> let xx = Const x in (Hashtbl.add (!table).c2t x xx; xx)
      [@@inline ]
    let fresh_global_constant () =
      (!table).frozen_constants <- ((!table).frozen_constants - 1);
      (let n = (!table).frozen_constants in
       let xx = Const n in
       Hashtbl.add (!table).c2s n ("frozen-" ^ (string_of_int n));
       Hashtbl.add (!table).c2t n xx;
       (n, xx))
    module Map = Constants.Map
    module Set = Constants.Set
    let rec mkinterval depth argsno n =
      if n = argsno
      then []
      else (mkConst (n + depth)) :: (mkinterval depth argsno (n + 1))
    let mkAppL c = function | [] -> mkConst c | x::xs -> mkApp c x xs
      [@@inline ]
  end 
let mkConst = C.mkConst
type 'args deref_fun =
  ?avoid:uvar_body -> from:int -> to_:int -> 'args -> term -> term
module Pp :
  sig
    val ppterm :
      ?pp_ctx:pp_ctx ->
        ?min_prec:int ->
          int -> string list -> int -> env -> Fmt.formatter -> term -> unit
    val uppterm :
      ?pp_ctx:pp_ctx ->
        ?min_prec:int ->
          int -> string list -> int -> env -> Fmt.formatter -> term -> unit
    val do_deref : int deref_fun ref
    val do_app_deref : term list deref_fun ref
    val uv_names : (string PtrMap.t * int) Fork.local_ref
    val pp_oref :
      ?pp_ctx:pp_ctx -> Format.formatter -> (Util.UUID.t * Obj.t) -> unit
    val pp_constant : ?pp_ctx:pp_ctx -> Format.formatter -> constant -> unit
  end =
  struct
    let do_deref =
      ref
        (fun ?avoid ->
           fun ~from -> fun ~to_ -> fun _ -> fun _ -> assert false)
    let do_app_deref =
      ref
        (fun ?avoid ->
           fun ~from -> fun ~to_ -> fun _ -> fun _ -> assert false)
    let uv_names = Fork.new_local ((PtrMap.empty ()), 0)
    let min_prec = Parser.min_precedence
    let appl_prec = Parser.appl_precedence
    let lam_prec = Parser.lam_precedence
    let inf_prec = Parser.inf_precedence
    let xppterm ~nice  ?(pp_ctx=
      { Data.uv_names = uv_names; table = (!C.table) })  ?(min_prec=
      min_prec)  depth0 names argsdepth env f t =
      let pp_app f pphd pparg ?pplastarg  (hd, args) =
        if args = []
        then pphd f hd
        else
          Fmt.fprintf f "@[<hov 1>%a@ %a@]" pphd hd
            (pplist pparg ?pplastelem:pplastarg " ") args in
      let ppconstant f c =
        Fmt.fprintf f "%s" (C.show ~table:(pp_ctx.table) c) in
      let rec pp_uvar prec depth vardepth args f r =
        if (!! r) == C.dummy
        then
          let s =
            try PtrMap.find r (fst (!(pp_ctx.uv_names)))
            with
            | Not_found ->
                let (m, n) = !(pp_ctx.uv_names) in
                let s = "X" ^ (string_of_int n) in
                let n = n + 1 in
                let m = PtrMap.add r s m in (pp_ctx.uv_names := (m, n); s) in
          Fmt.fprintf f "%s%s%s" s
            (if vardepth = 0 then "" else "^" ^ (string_of_int vardepth))
            (if args = 0 then "" else "+" ^ (string_of_int args))
        else
          if nice
          then
            aux prec depth f
              ((!do_deref) ~from:vardepth ~to_:depth args (!! r))
          else
            Fmt.fprintf f "<%a>_%d" (aux min_prec vardepth) (!! r) vardepth
      and pp_arg prec depth f n =
        let name =
          try List.nth names n with | Failure _ -> "A" ^ (string_of_int n) in
        if try (env.(n)) == C.dummy with | Invalid_argument _ -> true
        then Fmt.fprintf f "%s" name
        else
          if nice
          then
            (if argsdepth <= depth
             then
               let dereffed =
                 (!do_deref) ~from:argsdepth ~to_:depth 0 (env.(n)) in
               aux prec depth f dereffed
             else
               Fmt.fprintf f "\226\137\170%a\226\137\171_%d"
                 (aux min_prec argsdepth) (env.(n)) argsdepth)
          else
            Fmt.fprintf f "\226\137\170%a\226\137\171_%d"
              (aux min_prec argsdepth) (env.(n)) argsdepth
      and flat_cons_to_list depth acc t =
        match t with
        | UVar (r, vardepth, terms) when (!! r) != C.dummy ->
            flat_cons_to_list depth acc
              ((!do_deref) ~from:vardepth ~to_:depth terms (!! r))
        | AppUVar (r, vardepth, terms) when (!! r) != C.dummy ->
            flat_cons_to_list depth acc
              ((!do_app_deref) ~from:vardepth ~to_:depth terms (!! r))
        | Cons (x, y) -> flat_cons_to_list depth (x :: acc) y
        | _ -> ((List.rev acc), t)
      and is_lambda depth =
        function
        | Lam _ -> true
        | UVar (r, vardepth, terms) when (!! r) != C.dummy ->
            is_lambda depth
              ((!do_deref) ~from:vardepth ~to_:depth terms (!! r))
        | AppUVar (r, vardepth, terms) when (!! r) != C.dummy ->
            is_lambda depth
              ((!do_app_deref) ~from:vardepth ~to_:depth terms (!! r))
        | _ -> false
      and aux_last prec depth f t =
        if nice
        then
          match t with
          | Lam _ -> aux min_prec depth f t
          | UVar (r, vardepth, terms) when (!! r) != C.dummy ->
              aux_last prec depth f
                ((!do_deref) ~from:vardepth ~to_:depth terms (!! r))
          | AppUVar (r, vardepth, terms) when (!! r) != C.dummy ->
              aux_last prec depth f
                ((!do_app_deref) ~from:vardepth ~to_:depth terms (!! r))
          | _ -> aux prec depth f t
        else aux inf_prec depth f t
      and aux prec depth f t =
        let with_parens ?(test= true)  myprec h =
          if test && (myprec < prec)
          then (Fmt.fprintf f "("; h (); Fmt.fprintf f ")")
          else h () in
        match t with
        | Cons _|Nil ->
            let (prefix, last) = flat_cons_to_list depth [] t in
            (Fmt.fprintf f "[";
             pplist ~boxed:true (aux Parser.list_element_prec depth) ", " f
               prefix;
             if last != Nil then (Fmt.fprintf f " | "; aux prec 1 f last);
             Fmt.fprintf f "]")
        | Const s -> ppconstant f s
        | App (hd, x, xs) ->
            (try
               let (assoc, hdlvl) =
                 Parser.precedence_of (F.from_string (C.show hd)) in
               with_parens hdlvl
                 (fun _ ->
                    match assoc with
                    | Parser.Infix when (List.length xs) = 1 ->
                        Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
                          (aux (hdlvl + 1) depth) x ppconstant hd
                          (aux (hdlvl + 1) depth) (List.hd xs)
                    | Parser.Infixl when (List.length xs) = 1 ->
                        Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
                          (aux hdlvl depth) x ppconstant hd
                          (aux (hdlvl + 1) depth) (List.hd xs)
                    | Parser.Infixr when (List.length xs) = 1 ->
                        Fmt.fprintf f "@[<hov 1>%a@ %a@ %a@]"
                          (aux (hdlvl + 1) depth) x ppconstant hd
                          (aux hdlvl depth) (List.hd xs)
                    | Parser.Prefix when xs = [] ->
                        Fmt.fprintf f "@[<hov 1>%a@ %a@]" ppconstant hd
                          (aux hdlvl depth) x
                    | Parser.Postfix when xs = [] ->
                        Fmt.fprintf f "@[<hov 1>%a@ %a@]" (aux hdlvl depth) x
                          ppconstant hd
                    | _ ->
                        pp_app f ppconstant (aux inf_prec depth)
                          ~pplastarg:(aux_last inf_prec depth)
                          (hd, (x :: xs)))
             with
             | Not_found ->
                 let lastarg = List.nth (x :: xs) (List.length xs) in
                 let hdlvl =
                   if is_lambda depth lastarg
                   then lam_prec
                   else if hd == Global_symbols.andc then 110 else appl_prec in
                 with_parens hdlvl
                   (fun _ ->
                      if hd == Global_symbols.andc
                      then
                        pplist (aux inf_prec depth)
                          ~pplastelem:(aux_last inf_prec depth) ", " f (x ::
                          xs)
                      else
                        pp_app f ppconstant (aux inf_prec depth)
                          ~pplastarg:(aux_last inf_prec depth)
                          (hd, (x :: xs))))
        | Builtin (hd, xs) ->
            with_parens appl_prec
              (fun _ ->
                 pp_app f ppconstant (aux inf_prec depth)
                   ~pplastarg:(aux_last inf_prec depth) (hd, xs))
        | UVar (r, vardepth, argsno) when not nice ->
            let args = List.map destConst (C.mkinterval vardepth argsno 0) in
            with_parens ~test:(args <> []) appl_prec
              (fun _ ->
                 Fmt.fprintf f ".";
                 pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant
                   (r, args))
        | UVar (r, vardepth, argsno) when (!! r) == C.dummy ->
            let diff = vardepth - depth0 in
            let diff = if diff >= 0 then diff else 0 in
            let vardepth = vardepth - diff in
            let argsno = argsno + diff in
            let args = List.map destConst (C.mkinterval vardepth argsno 0) in
            with_parens ~test:(args <> []) appl_prec
              (fun _ ->
                 pp_app f (pp_uvar inf_prec depth vardepth 0) ppconstant
                   (r, args))
        | UVar (r, vardepth, argsno) ->
            pp_uvar prec depth vardepth argsno f r
        | AppUVar (r, vardepth, terms) when ((!! r) != C.dummy) && nice ->
            aux prec depth f
              ((!do_app_deref) ~from:vardepth ~to_:depth terms (!! r))
        | AppUVar (r, vardepth, terms) ->
            with_parens appl_prec
              (fun _ ->
                 pp_app f (pp_uvar inf_prec depth vardepth 0)
                   (aux inf_prec depth) ~pplastarg:(aux_last inf_prec depth)
                   (r, terms))
        | Arg (n, argsno) ->
            let args = List.map destConst (C.mkinterval argsdepth argsno 0) in
            with_parens ~test:(args <> []) appl_prec
              (fun _ -> pp_app f (pp_arg prec depth) ppconstant (n, args))
        | AppArg (v, terms) ->
            with_parens appl_prec
              (fun _ ->
                 pp_app f (pp_arg inf_prec depth) (aux inf_prec depth)
                   ~pplastarg:(aux_last inf_prec depth) (v, terms))
        | Lam t ->
            with_parens lam_prec
              (fun _ ->
                 let c = mkConst depth in
                 Fmt.fprintf f "%a \\@ %a" (aux inf_prec depth) c
                   (aux min_prec (depth + 1)) t)
        | CData d -> CData.pp f d
        | Discard -> Fmt.fprintf f "_" in
      try aux min_prec depth0 f t
      with | e -> Fmt.fprintf f "EXN PRINTING: %s" (Printexc.to_string e)
    let ppterm = xppterm ~nice:false
    let uppterm = xppterm ~nice:true
    let pp_oref ?pp_ctx  fmt (id, t) =
      if not (UUID.equal id id_term)
      then anomaly "pp_oref"
      else
        (let t : term = Obj.obj t in
         if t == C.dummy
         then Fmt.fprintf fmt "_"
         else uppterm ?pp_ctx 0 [] 0 empty_env fmt t)
    let pp_constant ?pp_ctx  fmt c =
      let table =
        match pp_ctx with | None -> None | Some { table } -> Some table in
      C.pp ?table fmt c
  end 
open Pp
let (rid, max_runtime_id) = ((Fork.new_local 0), (ref 0))
let auxsg = ref []
let get_auxsg sg l =
  let rec aux i =
    function
    | [] -> assert false
    | hd::tl -> if hd == sg then pred i else aux (pred i) tl in
  aux (List.length l) l
module ConstraintStoreAndTrail :
  sig
    type propagation_item =
      {
      cstr: constraint_def ;
      cstr_blockers: uvar_body list }
    val new_delayed : propagation_item list ref
    val to_resume : stuck_goal list ref
    val declare_new : stuck_goal -> unit
    val remove_old : stuck_goal -> unit
    val remove_old_constraint : constraint_def -> unit
    val contents :
      ?overlapping:uvar_body list -> unit -> (constraint_def * blockers) list
    val print :
      ?pp_ctx:pp_ctx ->
        Fmt.formatter -> (constraint_def * blockers) list -> unit
    val pp_stuck_goal : ?pp_ctx:pp_ctx -> Fmt.formatter -> stuck_goal -> unit
    val state : State.t Fork.local_ref
    type trail
    val empty : trail
    val initial_trail : trail Fork.local_ref
    val trail : trail Fork.local_ref
    val cut_trail : unit -> unit[@@inline ]
    val last_call : bool ref
    val trail_assignment : uvar_body -> unit[@@inline ]
    val trail_stuck_goal_addition : stuck_goal -> unit[@@inline ]
    val trail_stuck_goal_removal : stuck_goal -> unit[@@inline ]
    val undo : old_trail:trail -> ?old_state:State.t -> unit -> unit
    val print_trail : Fmt.formatter -> unit
    module Ugly : sig val delayed : stuck_goal list ref end
  end =
  struct
    type propagation_item =
      {
      cstr: constraint_def ;
      cstr_blockers: uvar_body list }
    let state =
      Fork.new_local
        ((((State.init ()) |> State.begin_goal_compilation) |>
            (State.end_goal_compilation StrMap.empty))
           |> State.end_compilation)
    let read_custom_constraint ct = State.get ct (!state)
    let update_custom_constraint ct f = state := (State.update ct (!state) f)
    type trail_item =
      | Assignement of uvar_body 
      | StuckGoalAddition of stuck_goal 
      | StuckGoalRemoval of stuck_goal [@@deriving show]
    include struct let _ = fun (_ : trail_item) -> () end[@@ocaml.doc
                                                           "@inline"]
    [@@merlin.hide ]
    let rec pp_trail_item :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        trail_item -> Ppx_deriving_runtime_proxy.unit
      =
      let __2 () = pp_stuck_goal
      and __1 () = pp_stuck_goal
      and __0 () = pp_uvar_body in
      ((let open! Ppx_deriving_runtime_proxy in
          fun fmt ->
            function
            | Assignement a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Runtime_trace_on.ConstraintStoreAndTrail.Assignement@ ";
                 ((__0 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | StuckGoalAddition a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Runtime_trace_on.ConstraintStoreAndTrail.StuckGoalAddition@ ";
                 ((__1 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])")
            | StuckGoalRemoval a0 ->
                (Ppx_deriving_runtime_proxy.Format.fprintf fmt
                   "(@[<2>Runtime_trace_on.ConstraintStoreAndTrail.StuckGoalRemoval@ ";
                 ((__2 ()) fmt) a0;
                 Ppx_deriving_runtime_proxy.Format.fprintf fmt "@])"))
        [@ocaml.warning "-A"])
    and show_trail_item : trail_item -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_trail_item x
    [@@ocaml.warning "-32"]
    type trail = trail_item list[@@deriving show]
    include struct let _ = fun (_ : trail) -> () end[@@ocaml.doc "@inline"]
    [@@merlin.hide ]
    let rec pp_trail :
      Ppx_deriving_runtime_proxy.Format.formatter ->
        trail -> Ppx_deriving_runtime_proxy.unit
      =
      let __0 () = pp_trail_item in
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
    and show_trail : trail -> Ppx_deriving_runtime_proxy.string =
      fun x -> Ppx_deriving_runtime_proxy.Format.asprintf "%a" pp_trail x[@@ocaml.warning
                                                                    "-32"]
    let empty = []
    let trail = Fork.new_local []
    let initial_trail = Fork.new_local []
    let last_call = Fork.new_local false
    let cut_trail () = trail := (!initial_trail)[@@inline ]
    module Ugly =
      struct let delayed : stuck_goal list ref = Fork.new_local [] end
    open Ugly
    let contents ?overlapping  () =
      let overlap : uvar_body list -> bool =
        match overlapping with
        | None -> (fun _ -> true)
        | Some l -> (fun b -> List.exists (fun x -> List.memq x l) b) in
      map_filter
        (function
         | { kind = Constraint c; blockers } when overlap blockers ->
             Some (c, blockers)
         | _ -> None) (!delayed)
    let trail_assignment x =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:trail:assign"
          [Trace_ppx_runtime.Runtime.J (Fmt.pp_print_bool, (!last_call));
          Trace_ppx_runtime.Runtime.J (pp_trail_item, (Assignement x))];
      if not (!last_call) then trail := ((Assignement x) :: (!trail))
      [@@inline ]
    let trail_stuck_goal_addition x =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          "dev:trail:add-constraint"
          [Trace_ppx_runtime.Runtime.J (Fmt.pp_print_bool, (!last_call));
          Trace_ppx_runtime.Runtime.J (pp_trail_item, (StuckGoalAddition x))];
      if not (!last_call) then trail := ((StuckGoalAddition x) :: (!trail))
      [@@inline ]
    let trail_stuck_goal_removal x =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          "dev:trail:remove-constraint"
          [Trace_ppx_runtime.Runtime.J (Fmt.pp_print_bool, (!last_call));
          Trace_ppx_runtime.Runtime.J (pp_trail_item, (StuckGoalRemoval x))];
      if not (!last_call) then trail := ((StuckGoalRemoval x) :: (!trail))
      [@@inline ]
    let remove ({ blockers } as sg) =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          "dev:constraint:remove"
          [Trace_ppx_runtime.Runtime.J (pp_stuck_goal, sg)];
      delayed := (remove_from_list sg (!delayed));
      List.iter (fun r -> r.rest <- (remove_from_list sg r.rest)) blockers
    let add ({ blockers } as sg) =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          "dev:constraint:add"
          [Trace_ppx_runtime.Runtime.J (pp_stuck_goal, sg)];
      auxsg := (sg :: (!auxsg));
      delayed := (sg :: (!delayed));
      List.iter (fun r -> r.rest <- (sg :: (r.rest))) blockers
    let new_delayed = Fork.new_local []
    let to_resume = Fork.new_local []
    let print_trail fmt =
      pp_trail fmt (!trail);
      Fmt.fprintf fmt "to_resume:%d new_delayed:%d\n%!"
        (List.length (!to_resume)) (List.length (!new_delayed))
    let declare_new sg =
      let blockers = uniqq sg.blockers in
      let sg = { sg with blockers } in
      add sg;
      (match sg.kind with
       | Unification _ -> ()
       | Constraint cstr ->
           new_delayed := ({ cstr; cstr_blockers = (sg.blockers) } ::
             (!new_delayed))
       | _ -> assert false);
      ((trail_stuck_goal_addition)[@inlined ]) sg
    let remove_cstr_if_exists x l =
      let rec aux acc =
        function
        | [] -> l
        | { cstr = y }::tl when x == y -> (List.rev acc) @ tl
        | y::tl -> aux (y :: acc) tl in
      aux [] l
    let remove_old cstr =
      remove cstr;
      (match cstr.kind with
       | Unification _ -> ()
       | Constraint c ->
           new_delayed := (remove_cstr_if_exists c (!new_delayed))
       | _ -> assert false);
      ((trail_stuck_goal_removal)[@inlined ]) cstr
    let remove_old_constraint cd =
      let c =
        List.find
          (function | { kind = Constraint x } -> x == cd | _ -> false)
          (!delayed) in
      remove_old c
    let undo ~old_trail  ?old_state  () =
      to_resume := [];
      new_delayed := [];
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:trail:undo"
          [Trace_ppx_runtime.Runtime.J (pp_trail, (!trail));
          Trace_ppx_runtime.Runtime.J (pp_string, "->");
          Trace_ppx_runtime.Runtime.J (pp_trail, old_trail)];
      while (!trail) != old_trail do
        (match !trail with
         | (Assignement r)::rest -> (r.contents <- C.dummy; trail := rest)
         | (StuckGoalAddition sg)::rest -> (remove sg; trail := rest)
         | (StuckGoalRemoval sg)::rest -> (add sg; trail := rest)
         | [] -> anomaly "undo to unknown trail")
        done;
      (match old_state with
       | Some old_state -> state := old_state
       | None -> ())
    let print ?pp_ctx  fmt x =
      let pp_depth fmt d =
        if d > 0
        then
          Fmt.fprintf fmt "{%a} :@ "
            (pplist (uppterm ?pp_ctx d [] 0 empty_env) " ")
            (C.mkinterval 0 d 0) in
      let pp_hyps fmt ctx =
        if ctx <> []
        then
          Fmt.fprintf fmt "@[<hov 2>%a@]@ ?- "
            (pplist
               (fun fmt ->
                  fun { hdepth = d; hsrc = t } ->
                    uppterm ?pp_ctx d [] 0 empty_env fmt t) ", ") ctx in
      let pp_goal depth = uppterm ?pp_ctx depth [] 0 empty_env in
      pplist
        (fun fmt ->
           fun
             ({ cdepth = depth; context = pdiff; conclusion = g }, blockers)
             ->
             Fmt.fprintf fmt
               " @[<h>@[<hov 2>%a%a%a@]@  /* suspended on %a */@]" pp_depth
               depth pp_hyps pdiff (pp_goal depth) g
               (pplist (uppterm ?pp_ctx 0 [] 0 empty_env) ", ")
               (List.map (fun r -> UVar (r, 0, 0)) blockers)) " " fmt x
    let pp_stuck_goal ?pp_ctx  fmt { kind; blockers } =
      match kind with
      | Unification { adepth = ad; env = e; bdepth = bd; a; b } ->
          Fmt.fprintf fmt
            " @[<h>@[<hov 2>^%d:%a@ == ^%d:%a@]@  /* suspended on %a */@]" ad
            (uppterm ?pp_ctx ad [] 0 empty_env) a bd
            (uppterm ?pp_ctx ad [] ad e) b
            (pplist ~boxed:false (uppterm ?pp_ctx 0 [] 0 empty_env) ", ")
            (List.map (fun r -> UVar (r, 0, 0)) blockers)
      | Constraint c -> print ?pp_ctx fmt [(c, blockers)]
      | _ -> assert false
  end 
module T = ConstraintStoreAndTrail
module CS = ConstraintStoreAndTrail
let (@:=) r v =
  ((T.trail_assignment)[@inlined ]) r;
  if r.rest <> []
  then
    (if true
     then
       Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
         "user:assign(resume)"
         [Trace_ppx_runtime.Runtime.J
            (((fun fmt ->
                 fun l ->
                   let l =
                     map_filter
                       (function
                        | { kind = Constraint { cgid;_};_} -> Some cgid
                        | _ -> None) l in
                   Fmt.fprintf fmt "%a" (pplist ~boxed:true UUID.pp " ") l)),
              (r.rest))];
     CS.to_resume :=
       (List.fold_right
          (fun x -> fun acc -> if List.memq x acc then acc else x :: acc)
          r.rest (!CS.to_resume)));
  r.contents <- v
module HO :
  sig
    val unif :
      matching:bool ->
        ((UUID.t)[@trace ]) -> int -> env -> int -> term -> term -> bool
    val move :
      adepth:int ->
        env -> ?avoid:uvar_body -> from:int -> to_:int -> term -> term
    val hmove : ?avoid:uvar_body -> from:int -> to_:int -> term -> term
    val subst : int -> term list -> term -> term
    val deref_uv : int deref_fun
    val deref_appuv : term list deref_fun
    val mkAppUVar : uvar_body -> int -> term list -> term
    val mkAppArg : int -> int -> term list -> term
    val is_flex : depth:int -> term -> uvar_body option
    val list_to_lp_list : term list -> term
    val mknLam : int -> term -> term
    val full_deref : adepth:int -> env -> depth:int -> term -> term
    val deref_head : depth:int -> term -> term
    type assignment = (uvar_body * int * term)
    val expand_uv :
      depth:int ->
        uvar_body -> lvl:int -> ano:int -> (term * assignment option)
    val expand_appuv :
      depth:int ->
        uvar_body -> lvl:int -> args:term list -> (term * assignment option)
    val shift_bound_vars : depth:int -> to_:int -> term -> term
    val subtract_to_consts : amount:int -> depth:int -> term -> term
    val delay_hard_unif_problems : bool Fork.local_ref
  end =
  struct
    exception NotInTheFragment 
    let rec in_fragment expected =
      function
      | [] -> 0
      | (Const c)::tl when c = expected ->
          1 + (in_fragment (expected + 1) tl)
      | (UVar ({ contents = t }, _, _))::tl -> in_fragment expected (t :: tl)
      | _ -> raise NotInTheFragment
    exception NonMetaClosed 
    let deterministic_restriction e ~args_safe  t =
      let rec aux =
        function
        | Lam f -> aux f
        | App (_, t, l) -> (aux t; List.iter aux l)
        | Cons (x, xs) -> (aux x; aux xs)
        | Builtin (_, l) -> List.iter aux l
        | UVar (r, _, _)|AppUVar (r, _, _) when (!! r) == C.dummy ->
            raise NonMetaClosed
        | UVar (r, _, _) -> aux (!! r)
        | AppUVar (r, _, l) -> (aux (!! r); List.iter aux l)
        | Arg (i, _) when ((e.(i)) == C.dummy) && (not args_safe) ->
            raise NonMetaClosed
        | AppArg (i, _) when (e.(i)) == C.dummy -> raise NonMetaClosed
        | Arg (i, _) -> if (e.(i)) != C.dummy then aux (e.(i))
        | AppArg (i, l) -> (aux (e.(i)); List.iter aux l)
        | Const _|Nil|Discard|CData _ -> () in
      try aux t; true with | NonMetaClosed -> false
    exception RestrictionFailure 
    let occurr_check r1 r2 =
      match r1 with
      | None -> ()
      | Some r1 -> if r1 == r2 then raise RestrictionFailure
    let rec make_lambdas destdepth args =
      if args = 0
      then let x = UVar ((oref C.dummy), destdepth, 0) in (x, x)
      else
        (let (x, y) = make_lambdas (destdepth + 1) (args - 1) in ((Lam x), y))
    let rec mknLam n x = if n = 0 then x else Lam (mknLam (n - 1) x)
    let mkAppUVar r lvl l =
      try UVar (r, lvl, (in_fragment lvl l))
      with | NotInTheFragment -> AppUVar (r, lvl, l)
    let mkAppArg i fromdepth xxs' =
      try Arg (i, (in_fragment fromdepth xxs'))
      with | NotInTheFragment -> AppArg (i, xxs')
    let expand_uv r ~lvl  ~ano  =
      let args = C.mkinterval 0 (lvl + ano) 0 in
      if lvl = 0
      then ((AppUVar (r, lvl, args)), None)
      else
        (let r1 = oref C.dummy in
         let t = AppUVar (r1, 0, args) in
         let assignment = mknLam ano t in (t, (Some (r, lvl, assignment))))
    let expand_uv ~depth  r ~lvl  ~ano  =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:expand_uv:in"
          [Trace_ppx_runtime.Runtime.J
             ((uppterm depth [] 0 empty_env), (UVar (r, lvl, ano)))];
      (let (t, ass) as rc = expand_uv r ~lvl ~ano in
       if true
       then
         Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
           "dev:expand_uv:out"
           [Trace_ppx_runtime.Runtime.J ((uppterm depth [] 0 empty_env), t);
           Trace_ppx_runtime.Runtime.J
             (((fun fmt ->
                  function
                  | None -> Fmt.fprintf fmt "no assignment"
                  | Some (_, _, t) ->
                      Fmt.fprintf fmt "%a := %a"
                        (uppterm depth [] 0 empty_env) (UVar (r, lvl, ano))
                        (uppterm lvl [] 0 empty_env) t)), ass)];
       rc)
    let expand_appuv r ~lvl  ~args  =
      if lvl = 0
      then ((AppUVar (r, lvl, args)), None)
      else
        (let args_lvl = C.mkinterval 0 lvl 0 in
         let r1 = oref C.dummy in
         let t = AppUVar (r1, 0, (args_lvl @ args)) in
         let nargs = List.length args in
         let assignment =
           mknLam nargs
             (AppUVar (r1, 0, (args_lvl @ (C.mkinterval lvl nargs 0)))) in
         (t, (Some (r, lvl, assignment))))
    let expand_appuv ~depth  r ~lvl  ~args  =
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          "dev:expand_appuv:in"
          [Trace_ppx_runtime.Runtime.J
             ((uppterm depth [] 0 empty_env), (AppUVar (r, lvl, args)))];
      (let (t, ass) as rc = expand_appuv r ~lvl ~args in
       if true
       then
         Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
           "dev:expand_appuv:out"
           [Trace_ppx_runtime.Runtime.J ((uppterm depth [] 0 empty_env), t);
           Trace_ppx_runtime.Runtime.J
             (((fun fmt ->
                  function
                  | None -> Fmt.fprintf fmt "no assignment"
                  | Some (_, _, t) ->
                      Fmt.fprintf fmt "%a := %a"
                        (uppterm depth [] 0 empty_env)
                        (AppUVar (r, lvl, args)) (uppterm lvl [] 0 empty_env)
                        t)), ass)];
       rc)
    let rec move ~adepth:argsdepth  e ?avoid  ~from  ~to_  t =
      let delta = from - to_ in
      let rc =
        if (delta = 0) && ((e == empty_env) && (avoid == None))
        then t
        else
          (let rec maux e depth x =
             let wall_clock = Unix.gettimeofday () in
             Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "move"
               (fun fmt ->
                  Format.fprintf fmt "adepth:%d depth:%d from:%d to:%d x:%a"
                    argsdepth depth from to_
                    (ppterm (from + depth) [] argsdepth e) x);
             (try
                let rc =
                  match x with
                  | Const c ->
                      if delta == 0
                      then x
                      else
                        if c >= from
                        then mkConst (c - delta)
                        else if c < to_ then x else raise RestrictionFailure
                  | Lam f ->
                      let f' = maux e (depth + 1) f in
                      if f == f' then x else Lam f'
                  | App (c, t, l) when
                      (delta == 0) || ((c < from) && (c < to_)) ->
                      let t' = maux e depth t in
                      let l' = smart_map (maux e depth) l in
                      if (t == t') && (l == l') then x else App (c, t', l')
                  | App (c, t, l) when c >= from ->
                      App
                        ((c - delta), (maux e depth t),
                          (smart_map (maux e depth) l))
                  | App _ -> raise RestrictionFailure
                  | Builtin (c, l) ->
                      let l' = smart_map (maux e depth) l in
                      if l == l' then x else Builtin (c, l')
                  | CData _ -> x
                  | Cons (hd, tl) ->
                      let hd' = maux e depth hd in
                      let tl' = maux e depth tl in
                      if (hd == hd') && (tl == tl')
                      then x
                      else Cons (hd', tl')
                  | Nil -> x
                  | Discard when avoid = None -> x
                  | Discard -> let r = oref C.dummy in UVar (r, to_, 0)
                  | UVar _ when (delta == 0) && (avoid == None) -> x
                  | UVar ({ contents = t }, vardepth, args) when t != C.dummy
                      ->
                      if depth == 0
                      then deref_uv ?avoid ~from:vardepth ~to_ args t
                      else
                        maux empty_env depth
                          (deref_uv ~from:vardepth ~to_:(from + depth) args t)
                  | AppUVar ({ contents = t }, vardepth, args) when
                      t != C.dummy ->
                      if depth == 0
                      then deref_appuv ?avoid ~from:vardepth ~to_ args t
                      else
                        maux empty_env depth
                          (deref_appuv ~from:vardepth ~to_:(from + depth)
                             args t)
                  | Arg (i, args) when (e.(i)) != C.dummy ->
                      deref_uv ?avoid ~from:argsdepth ~to_:(to_ + depth) args
                        (e.(i))
                  | AppArg (i, args) when (e.(i)) != C.dummy ->
                      let args =
                        try smart_map (maux e depth) args
                        with
                        | RestrictionFailure ->
                            anomaly
                              "move: could check if unrestrictable args are unused" in
                      deref_appuv ?avoid ~from:argsdepth ~to_:(to_ + depth)
                        args (e.(i))
                  | Arg (i, args) ->
                      let to_ = min argsdepth to_ in
                      let r = oref C.dummy in
                      let v = UVar (r, to_, 0) in
                      (e.(i) <- v;
                       if args == 0 then v else UVar (r, to_, args))
                  | AppArg (i, args) when
                      List.for_all
                        (deterministic_restriction e
                           ~args_safe:(argsdepth = to_)) args
                      ->
                      let to_ = min argsdepth to_ in
                      let args =
                        try List.map (maux e depth) args
                        with
                        | RestrictionFailure ->
                            anomaly
                              "TODO: implement deterministic restriction" in
                      let r = oref C.dummy in
                      let v = UVar (r, to_, 0) in
                      (e.(i) <- v; mkAppUVar r to_ args)
                  | AppArg _ ->
                      (Fmt.fprintf Fmt.str_formatter
                         "Non deterministic pruning, delay to be implemented: t=%a, delta=%d%!"
                         (ppterm depth [] argsdepth e) x delta;
                       anomaly (Fmt.flush_str_formatter ()))
                  | UVar (r, vardepth, argsno) ->
                      (occurr_check avoid r;
                       if delta <= 0
                       then
                         (if (vardepth + argsno) <= from
                          then x
                          else
                            (let (r, vardepth, argsno) =
                               decrease_depth r ~from:vardepth ~to_:from
                                 argsno in
                             let args = C.mkinterval vardepth argsno 0 in
                             let args = List.map (maux empty_env depth) args in
                             mkAppUVar r vardepth args))
                       else
                         if (vardepth + argsno) <= to_
                         then x
                         else
                           (let (t, assignment) =
                              expand_uv ~depth:(from + depth) r ~lvl:vardepth
                                ~ano:argsno in
                            option_iter
                              (fun (r, _, assignment) ->
                                 if true
                                 then
                                   Trace_ppx_runtime.Runtime.info
                                     ~runtime_id:(!rid) "user:assign(expand)"
                                     [Trace_ppx_runtime.Runtime.J
                                        (((fun fmt ->
                                             fun () ->
                                               Fmt.fprintf fmt "%a := %a"
                                                 (uppterm (from + depth) []
                                                    argsdepth e) x
                                                 (uppterm vardepth []
                                                    argsdepth e) assignment)),
                                          ())];
                                 r @:= assignment) assignment;
                            maux e depth t))
                  | AppUVar (r, vardepth, args) ->
                      (occurr_check avoid r;
                       if delta < 0
                       then
                         (let (r, vardepth, argsno) =
                            decrease_depth r ~from:vardepth ~to_:from 0 in
                          let args0 = C.mkinterval vardepth argsno 0 in
                          let args =
                            try List.map (maux e depth) (args0 @ args)
                            with
                            | RestrictionFailure ->
                                anomaly "impossible, delta < 0" in
                          mkAppUVar r vardepth args)
                       else
                         if delta == 0
                         then
                           AppUVar
                             (r, vardepth, (List.map (maux e depth) args))
                         else
                           if
                             List.for_all
                               (deterministic_restriction e
                                  ~args_safe:(argsdepth = to_)) args
                           then
                             (let pruned = ref (vardepth > to_) in
                              let orig_argsno = List.length args in
                              let filteredargs_vardepth = ref [] in
                              let filteredargs_to =
                                let rec filter i acc =
                                  function
                                  | [] ->
                                      (filteredargs_vardepth :=
                                         (List.rev acc);
                                       [])
                                  | arg::args ->
                                      (try
                                         let arg = maux e depth arg in arg ::
                                           (filter (succ i)
                                              ((mkConst (vardepth + i)) ::
                                              acc) args)
                                       with
                                       | RestrictionFailure ->
                                           (pruned := true;
                                            filter (succ i) acc args)) in
                                filter 0 [] args in
                              if !pruned
                              then
                                let vardepth' = min vardepth to_ in
                                let r' = oref C.dummy in
                                let newvar =
                                  mkAppUVar r' vardepth'
                                    (!filteredargs_vardepth) in
                                let assignment = mknLam orig_argsno newvar in
                                (if true
                                 then
                                   Trace_ppx_runtime.Runtime.info
                                     ~runtime_id:(!rid)
                                     "user:assign(restrict)"
                                     [Trace_ppx_runtime.Runtime.J
                                        (((fun fmt ->
                                             fun () ->
                                               Fmt.fprintf fmt "%d %a := %a"
                                                 vardepth
                                                 (ppterm (from + depth) []
                                                    argsdepth e) x
                                                 (ppterm vardepth []
                                                    argsdepth e) assignment)),
                                          ())];
                                 r @:= assignment;
                                 mkAppUVar r' vardepth' filteredargs_to)
                              else mkAppUVar r vardepth filteredargs_to)
                           else
                             (Fmt.fprintf Fmt.str_formatter
                                "Non deterministic pruning, delay to be implemented: t=%a, delta=%d%!"
                                (ppterm depth [] argsdepth e) x delta;
                              anomaly (Fmt.flush_str_formatter ()))) in
                let elapsed = (Unix.gettimeofday ()) -. wall_clock in
                Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "move"
                  false None elapsed;
                rc
              with
              | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
                  let elapsed = (Unix.gettimeofday ()) -. wall_clock in
                  (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "move"
                     true None elapsed;
                   Obj.obj f (Obj.obj x))
              | e ->
                  let elapsed = (Unix.gettimeofday ()) -. wall_clock in
                  (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "move"
                     false (Some e) elapsed;
                   raise e)) in
           maux e 0 t) in
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:move:out"
          [Trace_ppx_runtime.Runtime.J ((ppterm to_ [] argsdepth e), rc)];
      rc
    and hmove ?avoid  ~from  ~to_  t =
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "hmove"
        (fun fmt ->
           Format.fprintf fmt "@[<hov 1>from:%d@ to:%d@ %a@]" from to_
             (uppterm from [] 0 empty_env) t);
      (try
         let rc = move ?avoid ~adepth:0 ~from ~to_ empty_env t in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "hmove" false None
           elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "hmove" true
              None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "hmove" false
              (Some e) elapsed;
            raise e))
    and decrease_depth r ~from  ~to_  argsno =
      if from <= to_
      then (r, from, argsno)
      else
        (let newr = oref C.dummy in
         let newargsno = (argsno + from) - to_ in
         let newvar = UVar (newr, to_, (from - to_)) in
         r @:= newvar; (newr, to_, newargsno))
    and subst fromdepth ts t =
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "subst"
        (fun fmt ->
           Format.fprintf fmt "@[<hov 2>fromdepth:%d t: %a@ ts: %a@]"
             fromdepth (uppterm fromdepth [] 0 empty_env) t
             (pplist (uppterm fromdepth [] 0 empty_env) ", ") ts);
      (try
         let rc =
           if ts == []
           then t
           else
             (let len = List.length ts in
              let fromdepthlen = fromdepth + len in
              let rec aux depth tt =
                let wall_clock = Unix.gettimeofday () in
                Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid)
                  "subst-aux"
                  (fun fmt ->
                     Format.fprintf fmt "@[<hov 2>t: %a@]"
                       (uppterm (fromdepth + 1) [] 0 empty_env) tt);
                (try
                   let rc =
                     match tt with
                     | Const c as x ->
                         if (c >= fromdepth) && (c < fromdepthlen)
                         then
                           (match List.nth ts ((len - 1) - (c - fromdepth))
                            with
                            | Arg (i, 0) as t -> t
                            | t -> hmove ~from:fromdepth ~to_:(depth - len) t)
                         else if c < fromdepth then x else mkConst (c - len)
                     | Arg _|AppArg _ -> anomaly "subst takes a heap term"
                     | App (c, x, xs) as orig ->
                         let x' = aux depth x in
                         let xs' = List.map (aux depth) xs in
                         let xxs' = x' :: xs' in
                         if (c >= fromdepth) && (c < fromdepthlen)
                         then
                           (match List.nth ts ((len - 1) - (c - fromdepth))
                            with
                            | Arg (i, 0) -> mkAppArg i fromdepth xxs'
                            | t ->
                                let t =
                                  hmove ~from:fromdepth ~to_:(depth - len) t in
                                beta (depth - len) [] t xxs')
                         else
                           if c < fromdepth
                           then
                             (if (x == x') && (xs == xs')
                              then orig
                              else App (c, x', xs'))
                           else App ((c - len), x', xs')
                     | Builtin (c, xs) as orig ->
                         let xs' = List.map (aux depth) xs in
                         if xs == xs' then orig else Builtin (c, xs')
                     | Cons (hd, tl) as orig ->
                         let hd' = aux depth hd in
                         let tl' = aux depth tl in
                         if (hd == hd') && (tl == tl')
                         then orig
                         else Cons (hd', tl')
                     | Nil -> tt
                     | Discard -> tt
                     | UVar ({ contents = g }, vardepth, argsno) when
                         g != C.dummy ->
                         raise
                           (Trace_ppx_runtime.Runtime.TREC_CALL
                              ((Obj.repr (aux depth)),
                                (Obj.repr
                                   (deref_uv ~from:vardepth ~to_:depth argsno
                                      g))))
                     | UVar (r, vardepth, argsno) as orig ->
                         if (vardepth + argsno) <= fromdepth
                         then orig
                         else
                           (let (r, vardepth, argsno) =
                              decrease_depth r ~from:vardepth ~to_:fromdepth
                                argsno in
                            let args = C.mkinterval vardepth argsno 0 in
                            let args = List.map (aux depth) args in
                            mkAppUVar r vardepth args)
                     | AppUVar ({ contents = t }, vardepth, args) when
                         t != C.dummy ->
                         raise
                           (Trace_ppx_runtime.Runtime.TREC_CALL
                              ((Obj.repr (aux depth)),
                                (Obj.repr
                                   (deref_appuv ~from:vardepth ~to_:depth
                                      args t))))
                     | AppUVar (r, vardepth, args) ->
                         let (r, vardepth, argsno) =
                           decrease_depth r ~from:vardepth ~to_:fromdepth 0 in
                         let args0 = C.mkinterval vardepth argsno 0 in
                         let args = List.map (aux depth) (args0 @ args) in
                         mkAppUVar r vardepth args
                     | Lam t -> Lam (aux (depth + 1) t)
                     | CData _ as x -> x in
                   let elapsed = (Unix.gettimeofday ()) -. wall_clock in
                   Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid)
                     "subst-aux" false None elapsed;
                   rc
                 with
                 | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
                     let elapsed = (Unix.gettimeofday ()) -. wall_clock in
                     (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid)
                        "subst-aux" true None elapsed;
                      Obj.obj f (Obj.obj x))
                 | e ->
                     let elapsed = (Unix.gettimeofday ()) -. wall_clock in
                     (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid)
                        "subst-aux" false (Some e) elapsed;
                      raise e)) in
              aux fromdepthlen t) in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "subst" false None
           elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "subst" true
              None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "subst" false
              (Some e) elapsed;
            raise e))
    and beta depth sub t args =
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "beta"
        (fun fmt ->
           Format.fprintf fmt "@[<hov 2>subst@ t: %a@ args: %a@]"
             (uppterm (depth + (List.length sub)) [] 0 empty_env) t
             (pplist (uppterm depth [] 0 empty_env) ", ") args);
      (try
         let rc =
           match (t, args) with
           | (UVar ({ contents = g }, vardepth, argsno), _) when g != C.dummy
               ->
               raise
                 (Trace_ppx_runtime.Runtime.TREC_CALL
                    ((Obj.repr
                        (beta depth sub
                           (deref_uv ~from:vardepth
                              ~to_:(depth + (List.length sub)) argsno g))),
                      (Obj.repr args)))
           | (AppUVar ({ contents = g }, vardepth, uargs), _) when
               g != C.dummy ->
               raise
                 (Trace_ppx_runtime.Runtime.TREC_CALL
                    ((Obj.repr
                        (beta depth sub
                           (deref_appuv ~from:vardepth
                              ~to_:(depth + (List.length sub)) uargs g))),
                      (Obj.repr args)))
           | (Lam t', hd::tl) ->
               raise
                 (Trace_ppx_runtime.Runtime.TREC_CALL
                    ((Obj.repr (beta depth (hd :: sub) t')), (Obj.repr tl)))
           | _ ->
               let t' = subst depth sub t in
               (if true
                then
                  Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                    "dev:subst:out"
                    [Trace_ppx_runtime.Runtime.J
                       ((ppterm depth [] 0 empty_env), t')];
                (match args with
                 | [] -> t'
                 | ahd::atl ->
                     (match t' with
                      | Const c -> App (c, ahd, atl)
                      | Arg _|AppArg _ ->
                          anomaly "beta takes only heap terms"
                      | App (c, arg, args1) -> App (c, arg, (args1 @ args))
                      | Builtin (c, args1) -> Builtin (c, (args1 @ args))
                      | UVar (r, n, m) ->
                          (try UVar (r, n, (m + (in_fragment (n + m) args)))
                           with
                           | NotInTheFragment ->
                               let args1 = C.mkinterval n m 0 in
                               AppUVar (r, n, (args1 @ args)))
                      | AppUVar (r, depth, args1) ->
                          AppUVar (r, depth, (args1 @ args))
                      | Lam _ -> anomaly "beta: some args and some lambdas"
                      | CData x ->
                          type_error
                            (Printf.sprintf "beta: '%s'" (CData.show x))
                      | Nil -> type_error "beta: Nil"
                      | Cons _ -> type_error "beta: Cons"
                      | Discard -> type_error "beta: Discard"))) in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "beta" false None
           elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "beta" true
              None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "beta" false
              (Some e) elapsed;
            raise e))
    and eat_args depth l t =
      match t with
      | Lam t' when l > 0 -> eat_args (depth + 1) (l - 1) t'
      | UVar ({ contents = t }, origdepth, args) when t != C.dummy ->
          eat_args depth l (deref_uv ~from:origdepth ~to_:depth args t)
      | AppUVar ({ contents = t }, origdepth, args) when t != C.dummy ->
          eat_args depth l (deref_appuv ~from:origdepth ~to_:depth args t)
      | _ -> (depth, l, t)
    and deref_appuv ?avoid  ~from  ~to_  args t =
      beta to_ [] (deref_uv ?avoid ~from ~to_ 0 t) args
    and deref_uv ?avoid  ~from  ~to_  args t =
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "deref_uv"
        (fun fmt ->
           Format.fprintf fmt "from:%d to:%d %a @@ %d" from to_
             (ppterm from [] 0 empty_env) t args);
      (try
         let rc =
           if args == 0
           then hmove ?avoid ~from ~to_ t
           else
             (let (from, args', t) = eat_args from args t in
              let t = deref_uv ?avoid ~from ~to_ 0 t in
              if args' == 0
              then t
              else
                (match t with
                 | Lam _ -> anomaly "eat_args went crazy"
                 | Const c ->
                     let args = C.mkinterval (from + 1) (args' - 1) 0 in
                     App (c, (mkConst from), args)
                 | App (c, arg, args2) ->
                     let args = C.mkinterval from args' 0 in
                     App (c, arg, (args2 @ args))
                 | Builtin (c, args2) ->
                     let args = C.mkinterval from args' 0 in
                     Builtin (c, (args2 @ args))
                 | UVar (t, depth, args2) when from = (depth + args2) ->
                     UVar (t, depth, (args2 + args'))
                 | AppUVar (r, depth, args2) ->
                     let args = C.mkinterval from args' 0 in
                     AppUVar (r, depth, (args2 @ args))
                 | UVar (r, vardepth, argsno) ->
                     let args1 = C.mkinterval vardepth argsno 0 in
                     let args2 = C.mkinterval from args' 0 in
                     let args = args1 @ args2 in AppUVar (r, vardepth, args)
                 | Cons _|Nil -> type_error "deref_uv: applied list"
                 | Discard -> type_error "deref_uv: applied Discard"
                 | CData _ -> t
                 | Arg _|AppArg _ -> assert false)) in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "deref_uv" false
           None elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "deref_uv" true
              None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "deref_uv"
              false (Some e) elapsed;
            raise e))
    let rec is_flex ~depth  =
      function
      | Arg _|AppArg _ -> anomaly "is_flex called on Args"
      | UVar ({ contents = t }, vardepth, args) when t != C.dummy ->
          is_flex ~depth (deref_uv ~from:vardepth ~to_:depth args t)
      | AppUVar ({ contents = t }, vardepth, args) when t != C.dummy ->
          is_flex ~depth (deref_appuv ~from:vardepth ~to_:depth args t)
      | UVar (r, _, _)|AppUVar (r, _, _) -> Some r
      | Const _|Lam _|App _|Builtin _|CData _|Cons _|Nil|Discard -> None
    let is_llam lvl args adepth bdepth depth left e =
      let to_ = if left then adepth + depth else bdepth + depth in
      let get_con = function | Const x -> x | _ -> raise RestrictionFailure in
      let deref_to_const =
        function
        | UVar ({ contents = t }, from, args) when t != C.dummy ->
            get_con (deref_uv ~from ~to_ args t)
        | AppUVar ({ contents = t }, from, args) when t != C.dummy ->
            get_con (deref_appuv ~from ~to_ args t)
        | Arg (i, args) when (e.(i)) != C.dummy ->
            get_con (deref_uv ~from:adepth ~to_ args (e.(i)))
        | AppArg (i, args) when (e.(i)) != C.dummy ->
            get_con (deref_appuv ~from:adepth ~to_ args (e.(i)))
        | Const x ->
            if (not left) && (x >= bdepth) then x + (adepth - bdepth) else x
        | _ -> raise RestrictionFailure in
      let rec aux n =
        function
        | [] -> []
        | x::xs ->
            if (x >= lvl) && (not (List.mem x xs))
            then (x, n) :: (aux (n + 1) xs)
            else raise RestrictionFailure in
      try (true, (aux 0 (List.map deref_to_const args)))
      with | RestrictionFailure -> (false, [])
    let is_llam lvl args adepth bdepth depth left e =
      let res = is_llam lvl args adepth bdepth depth left e in
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:is_llam"
          [Trace_ppx_runtime.Runtime.J
             (((fun fmt ->
                  fun () ->
                    let (b, map) = res in
                    Fmt.fprintf fmt "%d + %a = %b, %a" lvl
                      (pplist (ppterm adepth [] bdepth e) " ") args b
                      (pplist
                         (fun fmt ->
                            fun (x, n) -> Fmt.fprintf fmt "%d |-> %d" x n)
                         " ") map)), ())];
      res
    let rec mknLam n t = if n = 0 then t else mknLam (n - 1) (Lam t)
    let bind r gamma l a d delta b left t e =
      let new_lams = List.length l in
      let pos x =
        try List.assoc x l with | Not_found -> raise RestrictionFailure in
      let cst ?(hmove= true)  c b delta =
        if left
        then
          (if (c < gamma) && (c < b)
           then c
           else
             (let c = if hmove && (c >= b) then c + delta else c in
              if c < gamma
              then c
              else
                if c >= (a + d)
                then (c + new_lams) - ((a + d) - gamma)
                else (pos c) + gamma))
        else
          if c < gamma
          then c
          else
            if c >= (a + d)
            then (c + new_lams) - ((a + d) - gamma)
            else (pos c) + gamma in
      let cst ?hmove  c b delta =
        let n = cst ?hmove c b delta in
        if true
        then
          Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
            "dev:bind:constant-mapping"
            [Trace_ppx_runtime.Runtime.J
               (((fun fmt ->
                    fun () ->
                      let (n, m) = (c, n) in
                      Fmt.fprintf fmt
                        "%d -> %d (c:%d b:%d gamma:%d delta:%d d:%d)" n m c b
                        gamma delta d)), ())];
        n in
      let rec bind b delta w t =
        let wall_clock = Unix.gettimeofday () in
        Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "bind"
          (fun fmt ->
             Format.fprintf fmt
               "%b gamma:%d + %a = t:%a a:%d delta:%d d:%d w:%d b:%d" left
               gamma
               (pplist
                  (fun fmt ->
                     fun (x, n) ->
                       Fmt.fprintf fmt "%a |-> %d" (ppterm a [] b e)
                         (mkConst x) n) " ") l (ppterm a [] b empty_env) t a
               delta d w b);
        (try
           let rc =
             match t with
             | UVar (r1, _, _)|AppUVar (r1, _, _) when r == r1 ->
                 raise RestrictionFailure
             | Const c ->
                 let n = cst c b delta in
                 if n < 0 then mkConst n else Const n
             | Lam t -> Lam (bind b delta (w + 1) t)
             | App (c, t, ts) ->
                 App
                   ((cst c b delta), (bind b delta w t),
                     (List.map (bind b delta w) ts))
             | Cons (hd, tl) ->
                 Cons ((bind b delta w hd), (bind b delta w tl))
             | Nil -> t
             | Builtin (c, tl) -> Builtin (c, (List.map (bind b delta w) tl))
             | CData _ -> t
             | Arg (i, args) when (e.(i)) != C.dummy ->
                 bind a 0 w
                   (deref_uv ~from:a ~to_:((a + d) + w) args (e.(i)))
             | AppArg (i, args) when (e.(i)) != C.dummy ->
                 bind a 0 w
                   (deref_appuv ~from:a ~to_:((a + d) + w) args (e.(i)))
             | UVar ({ contents = t }, from, args) when t != C.dummy ->
                 bind b delta w
                   (deref_uv ~from ~to_:(((if left then b else a) + d) + w)
                      args t)
             | AppUVar ({ contents = t }, from, args) when t != C.dummy ->
                 bind b delta w
                   (deref_appuv ~from
                      ~to_:(((if left then b else a) + d) + w) args t)
             | UVar _|AppUVar _|Arg _|AppArg _|Discard as orig ->
                 let (r, lvl, (is_llam, args), orig_args) =
                   match orig with
                   | UVar (r, lvl, 0) -> (r, lvl, (true, []), [])
                   | UVar (r, lvl, args) ->
                       let r' = oref C.dummy in
                       let v = UVar (r', (lvl + args), 0) in
                       (r @:= (mknLam args v);
                        (r', (lvl + args), (true, []), []))
                   | AppUVar (r, lvl, orig_args) ->
                       (r, lvl, (is_llam lvl orig_args a b (d + w) left e),
                         orig_args)
                   | Discard ->
                       let r = oref C.dummy in
                       (r, ((a + d) + w), (true, []), [])
                   | Arg (i, 0) ->
                       let r = oref C.dummy in
                       let v = UVar (r, a, 0) in
                       (e.(i) <- v; (r, a, (true, []), []))
                   | Arg (i, args) ->
                       let r = oref C.dummy in
                       let v = UVar (r, a, 0) in
                       (e.(i) <- v;
                        (let r' = oref C.dummy in
                         let v' = UVar (r', (a + args), 0) in
                         r @:= (mknLam args v');
                         (r', (a + args), (true, []), [])))
                   | AppArg (i, orig_args) ->
                       let (is_llam, args) =
                         is_llam a orig_args a b (d + w) false e in
                       let r = oref C.dummy in
                       let v = UVar (r, a, 0) in
                       (e.(i) <- v; (r, a, (is_llam, args), orig_args))
                   | _ -> assert false in
                 (if true
                  then
                    Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                      "dev:bind:maybe-prune"
                      [Trace_ppx_runtime.Runtime.J
                         (((fun fmt ->
                              fun () ->
                                Fmt.fprintf fmt
                                  "lvl:%d is_llam:%b args:%a orig_args:%a orig:%a"
                                  lvl is_llam
                                  (pplist
                                     (fun fmt ->
                                        fun (x, n) ->
                                          Fmt.fprintf fmt "%a->%d"
                                            (ppterm a [] b e) (mkConst x) n)
                                     " ") args (pplist (ppterm a [] b e) " ")
                                  orig_args (ppterm a [] b e) orig)), ())];
                  if is_llam
                  then
                    (let n_args = List.length args in
                     if lvl > gamma
                     then
                       let (args_gamma_lvl_abs, args_gamma_lvl_here) =
                         let mk_arg i =
                           ((mkConst i),
                             (mkConst (cst ~hmove:false i b delta))) in
                         let rec mk_interval d argsno n =
                           if n = argsno
                           then []
                           else
                             if (n + d) >= lvl
                             then
                               (let i = n + d in
                                try
                                  let nn = List.assoc i args in
                                  ((mkConst (lvl + nn)),
                                    (mkConst ((gamma + (List.length l)) + n)))
                                    :: (mk_interval d argsno (n + 1))
                                with
                                | Not_found -> mk_interval d argsno (n + 1))
                             else (mk_arg (n + d)) ::
                               (mk_interval d argsno (n + 1)) in
                         let rec keep_cst_for_lvl =
                           function
                           | [] ->
                               mk_interval (d + (if left then a else b)) w 0
                           | (i, mm)::rest ->
                               if i < lvl
                               then (mk_arg i) :: (keep_cst_for_lvl rest)
                               else
                                 (try
                                    let nn = List.assoc i args in
                                    ((mkConst (lvl + nn)), (mkConst mm)) ::
                                      (keep_cst_for_lvl rest)
                                  with | Not_found -> keep_cst_for_lvl rest) in
                         List.split
                           (keep_cst_for_lvl (List.sort Pervasives.compare l)) in
                       let r' = oref C.dummy in
                       (r @:=
                          (mknLam n_args
                             (mkAppUVar r' gamma args_gamma_lvl_abs));
                        mkAppUVar r' gamma args_gamma_lvl_here)
                     else
                       (let args = List.sort Pervasives.compare args in
                        let (args_lvl, args_here) =
                          List.fold_right
                            (fun (c, c_p) ->
                               fun ((a_lvl, a_here) as acc) ->
                                 try
                                   let i =
                                     if c < gamma
                                     then c
                                     else
                                       if c >= ((if left then b else a) + d)
                                       then
                                         (c + new_lams) - ((a + d) - gamma)
                                       else (pos c) + gamma in
                                   (((mkConst (c_p + lvl)) :: a_lvl),
                                     ((mkConst i) :: a_here))
                                 with | RestrictionFailure -> acc) args
                            ([], []) in
                        if n_args = (List.length args_here)
                        then
                          mkAppUVar r lvl
                            (List.map (bind b delta w) orig_args)
                        else
                          (let r' = oref C.dummy in
                           let v = mkAppUVar r' lvl args_lvl in
                           r @:= (mknLam n_args v);
                           mkAppUVar r' lvl args_here)))
                  else mkAppUVar r lvl (List.map (bind b delta w) orig_args)) in
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "bind" false
             None elapsed;
           rc
         with
         | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
             let elapsed = (Unix.gettimeofday ()) -. wall_clock in
             (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "bind" true
                None elapsed;
              Obj.obj f (Obj.obj x))
         | e ->
             let elapsed = (Unix.gettimeofday ()) -. wall_clock in
             (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "bind" false
                (Some e) elapsed;
              raise e)) in
      try
        let v = mknLam new_lams (bind b delta 0 t) in
        if true
        then
          Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "user:assign(HO)"
            [Trace_ppx_runtime.Runtime.J
               (((fun fmt ->
                    fun () ->
                      Fmt.fprintf fmt "%a := %a" (uppterm gamma [] a e)
                        (UVar (r, gamma, 0)) (uppterm gamma [] a e) v)), ())];
        r @:= v;
        true
      with
      | RestrictionFailure ->
          (if true
           then
             Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
               "dev:bind:restriction-failure" [];
           false)
    let rec list_to_lp_list =
      function | [] -> Nil | x::xs -> Cons (x, (list_to_lp_list xs))
    let delay_hard_unif_problems = Fork.new_local false
    let error_msg_hard_unif a b =
      "Unification problem outside the pattern fragment. (" ^
        ((show_term a) ^
           (" == " ^
              ((show_term b) ^
                 (") Pass -delay-problems-outside-pattern-fragment (elpi command line utility) "
                    ^
                    ("or set delay_outside_fragment to true (Elpi_API) in order to delay "
                       ^ "(deprecated, for Teyjus compatibility).")))))
    let rec unif matching depth adepth a bdepth b e =
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "unif"
        (fun fmt ->
           Format.fprintf fmt "@[<hov 2>^%d:%a@ =%d%s= ^%d:%a@]%!" adepth
             (ppterm (adepth + depth) [] adepth empty_env) a depth
             (if matching then "m" else "") bdepth
             (ppterm (bdepth + depth) [] adepth e) b);
      (try
         let rc =
           let delta = adepth - bdepth in
           ((delta = 0) && (a == b)) ||
             (match (a, b) with
              | (Discard, _)|(_, Discard) -> true
              | (_, App (c, arg, (Arg _|AppArg _ as as_this)::[])) when
                  c == Global_symbols.asc ->
                  (unif matching depth adepth a bdepth arg e) &&
                    (unif matching depth adepth a bdepth as_this e)
              | (_, App (c, arg, _)) when c == Global_symbols.asc ->
                  error "syntax error in as"
              | (App (c, arg, _), _) when c == Global_symbols.asc ->
                  unif matching depth adepth arg bdepth b e
              | (UVar (r1, _, args1), UVar (r2, _, args2)) when
                  (r1 == r2) && ((!! r1) == C.dummy) -> args1 == args2
              | (UVar (r1, vd, xs), AppUVar (r2, _, ys)) when
                  (r1 == r2) && ((!! r1) == C.dummy) ->
                  unif matching depth adepth
                    (AppUVar (r1, vd, (C.mkinterval vd xs 0))) bdepth b e
              | (AppUVar (r1, vd, xs), UVar (r2, _, ys)) when
                  (r1 == r2) && ((!! r1) == C.dummy) ->
                  unif matching depth adepth a bdepth
                    (AppUVar (r1, vd, (C.mkinterval vd ys 0))) e
              | (AppUVar (r1, vd, xs), AppUVar (r2, _, ys)) when
                  (r1 == r2) && ((!! r1) == C.dummy) ->
                  let pruned = ref false in
                  let filtered_args_rev =
                    fold_left2i
                      (fun i ->
                         fun args ->
                           fun x ->
                             fun y ->
                               let b =
                                 unif matching depth adepth x bdepth y e in
                               if not b
                               then (pruned := true; args)
                               else x :: args) [] xs ys in
                  (if !pruned
                   then
                     (let len = List.length xs in
                      let r = oref C.dummy in
                      r1 @:=
                        (mknLam len
                           (mkAppUVar r vd (List.rev filtered_args_rev))));
                   true)
              | (UVar ({ contents = t }, from, args), _) when t != C.dummy ->
                  unif matching depth adepth
                    (deref_uv ~from ~to_:(adepth + depth) args t) bdepth b e
              | (AppUVar ({ contents = t }, from, args), _) when t != C.dummy
                  ->
                  unif matching depth adepth
                    (deref_appuv ~from ~to_:(adepth + depth) args t) bdepth b
                    e
              | (_, UVar ({ contents = t }, from, args)) when t != C.dummy ->
                  unif matching depth adepth a bdepth
                    (deref_uv ~from ~to_:(bdepth + depth) args t) empty_env
              | (_, AppUVar ({ contents = t }, from, args)) when t != C.dummy
                  ->
                  unif matching depth adepth a bdepth
                    (deref_appuv ~from ~to_:(bdepth + depth) args t)
                    empty_env
              | (_, Arg (i, args)) when (e.(i)) != C.dummy ->
                  unif matching depth adepth a adepth
                    (deref_uv ~from:adepth ~to_:(adepth + depth) args (e.(i)))
                    empty_env
              | (_, AppArg (i, args)) when (e.(i)) != C.dummy ->
                  let args =
                    List.map (move ~adepth ~from:bdepth ~to_:adepth e) args in
                  unif matching depth adepth a adepth
                    (deref_appuv ~from:adepth ~to_:(adepth + depth) args
                       (e.(i))) empty_env
              | ((UVar _|AppUVar _), Const c) when
                  (c == Global_symbols.uvarc) && matching -> true
              | (UVar (r, vd, ano), App (c, hd, [])) when
                  (c == Global_symbols.uvarc) && matching ->
                  unif matching depth adepth (UVar (r, vd, ano)) bdepth hd e
              | (AppUVar (r, vd, _), App (c, hd, [])) when
                  (c == Global_symbols.uvarc) && matching ->
                  unif matching depth adepth (UVar (r, vd, 0)) bdepth hd e
              | (UVar (r, vd, ano), App (c, hd, arg::[])) when
                  (c == Global_symbols.uvarc) && matching ->
                  let r_exp = oref C.dummy in
                  let exp = UVar (r_exp, 0, 0) in
                  (r @:= (UVar (r_exp, 0, vd));
                   (unif matching depth adepth exp bdepth hd e) &&
                     ((let args =
                         list_to_lp_list (C.mkinterval 0 (vd + ano) 0) in
                       unif matching depth adepth args bdepth arg e)))
              | (AppUVar (r, vd, args), App (c, hd, arg::[])) when
                  (c == Global_symbols.uvarc) && matching ->
                  let r_exp = oref C.dummy in
                  let exp = UVar (r_exp, 0, 0) in
                  (r @:= (UVar (r_exp, 0, vd));
                   (unif matching depth adepth exp bdepth hd e) &&
                     ((let args =
                         list_to_lp_list ((C.mkinterval 0 vd 0) @ args) in
                       unif matching depth adepth args bdepth arg e)))
              | (_, (Const c|App (c, _, []))) when
                  (c == Global_symbols.uvarc) && matching -> false
              | (_, Arg (i, 0)) ->
                  (try
                     let v = hmove ~from:(adepth + depth) ~to_:adepth a in
                     if true
                     then
                       Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                         "user:assign"
                         [Trace_ppx_runtime.Runtime.J
                            (((fun fmt ->
                                 fun () ->
                                   Fmt.fprintf fmt "%a := %a"
                                     (uppterm adepth [] adepth e) b
                                     (uppterm adepth [] adepth e) v)), ())];
                     e.(i) <- v;
                     true
                   with | RestrictionFailure -> false)
              | (UVar ({ rest = [] }, _, 0), UVar ({ rest = _::_ }, _, 0)) ->
                  unif matching depth bdepth b adepth a e
              | (AppUVar ({ rest = [] }, _, _), UVar ({ rest = _::_ }, _, 0))
                  -> unif matching depth bdepth b adepth a e
              | (_, UVar (r, origdepth, 0)) ->
                  (try
                     let t =
                       if depth = 0
                       then hmove ~avoid:r ~from:adepth ~to_:origdepth a
                       else
                         (let a =
                            hmove ~avoid:r ~from:(adepth + depth)
                              ~to_:(bdepth + depth) a in
                          hmove ~from:(bdepth + depth) ~to_:origdepth a) in
                     if true
                     then
                       Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                         "user:assign"
                         [Trace_ppx_runtime.Runtime.J
                            (((fun fmt ->
                                 fun () ->
                                   Fmt.fprintf fmt "%a := %a"
                                     (uppterm depth [] bdepth e) b
                                     (uppterm depth [] bdepth e) t)), ())];
                     r @:= t;
                     true
                   with | RestrictionFailure -> false)
              | (UVar (r, origdepth, 0), _) when not matching ->
                  (try
                     let t =
                       if depth = 0
                       then
                         move ~avoid:r ~adepth ~from:bdepth ~to_:origdepth e
                           b
                       else
                         (let b =
                            move ~avoid:r ~adepth ~from:(bdepth + depth)
                              ~to_:(adepth + depth) e b in
                          hmove ~from:(adepth + depth) ~to_:origdepth b) in
                     if true
                     then
                       Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                         "user:assign"
                         [Trace_ppx_runtime.Runtime.J
                            (((fun fmt ->
                                 fun () ->
                                   Fmt.fprintf fmt "%a := %a"
                                     (uppterm origdepth [] 0 empty_env) a
                                     (uppterm origdepth [] 0 empty_env) t)),
                              ())];
                     r @:= t;
                     true
                   with | RestrictionFailure -> false)
              | (_, Arg (i, args)) ->
                  let v = fst (make_lambdas adepth args) in
                  (if true
                   then
                     Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                       "user:assign"
                       [Trace_ppx_runtime.Runtime.J
                          (((fun fmt ->
                               fun () ->
                                 Fmt.fprintf fmt "%a := %a"
                                   (uppterm depth [] bdepth e) (Arg (i, 0))
                                   (uppterm depth [] bdepth e) v)), ())];
                   e.(i) <- v;
                   if true
                   then
                     Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                       "user:assign"
                       [Trace_ppx_runtime.Runtime.J
                          (((fun fmt ->
                               fun () ->
                                 ppterm depth [] adepth empty_env fmt (e.(i)))),
                            ())];
                   unif matching depth adepth a bdepth b e)
              | (UVar ({ rest = [] }, _, a1), UVar ({ rest = _::_ }, _, a2))
                  when (a1 + a2) > 0 ->
                  unif matching depth bdepth b adepth a e
              | (AppUVar ({ rest = [] }, _, _), UVar
                 ({ rest = _::_ }, _, a2)) when a2 > 0 ->
                  unif matching depth bdepth b adepth a e
              | (_, UVar (r, origdepth, args)) when
                  (args > 0) &&
                    (match a with
                     | UVar (r1, _, _)|AppUVar (r1, _, _) -> r != r1
                     | _ -> true)
                  ->
                  let v = fst (make_lambdas origdepth args) in
                  (if true
                   then
                     Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                       "user:assign(simplify)"
                       [Trace_ppx_runtime.Runtime.J
                          (((fun fmt ->
                               fun () ->
                                 Fmt.fprintf fmt "%a := %a"
                                   (uppterm depth [] bdepth e)
                                   (UVar (r, origdepth, 0))
                                   (uppterm depth [] bdepth e) v)), ())];
                   r @:= v;
                   unif matching depth adepth a bdepth b e)
              | (UVar (r, origdepth, args), _) when
                  (args > 0) &&
                    (match b with
                     | UVar (r1, _, _)|AppUVar (r1, _, _) -> r != r1
                     | _ -> true)
                  ->
                  let v = fst (make_lambdas origdepth args) in
                  (if true
                   then
                     Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                       "user:assign(simplify)"
                       [Trace_ppx_runtime.Runtime.J
                          (((fun fmt ->
                               fun () ->
                                 Fmt.fprintf fmt "%a := %a"
                                   (uppterm depth [] adepth e)
                                   (UVar (r, origdepth, 0))
                                   (uppterm depth [] adepth e) v)), ())];
                   r @:= v;
                   unif matching depth adepth a bdepth b e)
              | (other, AppArg (i, args)) ->
                  let (is_llam, args) =
                    is_llam adepth args adepth bdepth depth false e in
                  if is_llam
                  then
                    let r = oref C.dummy in
                    (e.(i) <- (UVar (r, adepth, 0));
                     bind r adepth args adepth depth delta bdepth false other
                       e)
                  else
                    if !delay_hard_unif_problems
                    then
                      (Fmt.fprintf Fmt.std_formatter
                         "HO unification delayed: %a = %a\n%!"
                         (uppterm depth [] adepth empty_env) a
                         (uppterm depth [] bdepth e) b;
                       (let r = oref C.dummy in
                        e.(i) <- (UVar (r, adepth, 0));
                        (let kind =
                           Unification
                             {
                               adepth = (adepth + depth);
                               env = e;
                               bdepth = (bdepth + depth);
                               a;
                               b;
                               matching
                             } in
                         let blockers =
                           match is_flex (adepth + depth) other with
                           | None -> [r]
                           | Some r' -> if r == r' then [r] else [r; r'] in
                         CS.declare_new { kind; blockers }; true)))
                    else error (error_msg_hard_unif a b)
              | (AppUVar ({ rest = _::_ }, _, _),
                 (AppUVar ({ rest = [] }, _, _)|UVar ({ rest = [] }, _, _)))
                  -> unif matching depth bdepth b adepth a e
              | (AppUVar (r, lvl, args), other) when not matching ->
                  let (is_llam, args) =
                    is_llam lvl args adepth bdepth depth true e in
                  if is_llam
                  then bind r lvl args adepth depth delta bdepth true other e
                  else
                    if !delay_hard_unif_problems
                    then
                      (Fmt.fprintf Fmt.std_formatter
                         "HO unification delayed: %a = %a\n%!"
                         (uppterm depth [] adepth empty_env) a
                         (uppterm depth [] bdepth empty_env) b;
                       (let kind =
                          Unification
                            {
                              adepth = (adepth + depth);
                              env = e;
                              bdepth = (bdepth + depth);
                              a;
                              b;
                              matching
                            } in
                        let blockers =
                          match is_flex (bdepth + depth) other with
                          | None -> [r]
                          | Some r' -> [r; r'] in
                        CS.declare_new { kind; blockers }; true))
                    else error (error_msg_hard_unif a b)
              | (other, AppUVar (r, lvl, args)) ->
                  let (is_llam, args) =
                    is_llam lvl args adepth bdepth depth false e in
                  if is_llam
                  then
                    bind r lvl args adepth depth delta bdepth false other e
                  else
                    if !delay_hard_unif_problems
                    then
                      (Fmt.fprintf Fmt.std_formatter
                         "HO unification delayed: %a = %a\n%!"
                         (uppterm depth [] adepth empty_env) a
                         (uppterm depth [] bdepth e) b;
                       (let kind =
                          Unification
                            {
                              adepth = (adepth + depth);
                              env = e;
                              bdepth = (bdepth + depth);
                              a;
                              b;
                              matching
                            } in
                        let blockers =
                          match is_flex (adepth + depth) other with
                          | None -> [r]
                          | Some r' -> if r == r' then [r] else [r; r'] in
                        CS.declare_new { kind; blockers }; true))
                    else error (error_msg_hard_unif a b)
              | (App (c1, x2, xs), App (c2, y2, ys)) ->
                  ((((delta = 0) || (c1 < bdepth)) && (c1 = c2)) ||
                     ((c1 >= adepth) && (c1 = (c2 + delta))))
                    &&
                    ((((delta = 0) && (x2 == y2)) ||
                        (unif matching depth adepth x2 bdepth y2 e))
                       &&
                       (for_all2
                          (fun x ->
                             fun y -> unif matching depth adepth x bdepth y e)
                          xs ys))
              | (Builtin (c1, xs), Builtin (c2, ys)) ->
                  (c1 = c2) &&
                    (for_all2
                       (fun x ->
                          fun y -> unif matching depth adepth x bdepth y e)
                       xs ys)
              | (Lam t1, Lam t2) ->
                  unif matching (depth + 1) adepth t1 bdepth t2 e
              | (Const c1, Const c2) ->
                  if c1 < bdepth
                  then c1 = c2
                  else (c1 >= adepth) && (c1 = (c2 + delta))
              | (CData d1, CData d2) -> CData.equal d1 d2
              | (Cons (hd1, tl1), Cons (hd2, tl2)) ->
                  (unif matching depth adepth hd1 bdepth hd2 e) &&
                    (unif matching depth adepth tl1 bdepth tl2 e)
              | (Nil, Nil) -> true
              | (Lam t, Const c) ->
                  let extra = mkConst (bdepth + depth) in
                  let eta = App (c, extra, []) in
                  unif matching (depth + 1) adepth t bdepth eta e
              | (Const c, Lam t) ->
                  let extra = mkConst (adepth + depth) in
                  let eta = App (c, extra, []) in
                  unif matching (depth + 1) adepth eta bdepth t e
              | (Lam t, App (c, x, xs)) ->
                  let extra = mkConst (bdepth + depth) in
                  let motion =
                    move ~adepth ~from:(bdepth + depth)
                      ~to_:((bdepth + depth) + 1) e in
                  let x = motion x in
                  let xs = (List.map motion xs) @ [extra] in
                  let eta = App (c, x, xs) in
                  unif matching (depth + 1) adepth t bdepth eta e
              | (App (c, x, xs), Lam t) ->
                  let extra = mkConst (adepth + depth) in
                  let motion =
                    hmove ~from:(bdepth + depth) ~to_:((bdepth + depth) + 1) in
                  let x = motion x in
                  let xs = (List.map motion xs) @ [extra] in
                  let eta = App (c, x, xs) in
                  unif matching (depth + 1) adepth eta bdepth t e
              | _ -> false) in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "unif" false None
           elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "unif" true
              None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "unif" false
              (Some e) elapsed;
            raise e))
    let unif ~matching  ((gid)[@trace ]) adepth e bdepth a b =
      let res = unif matching 0 adepth a bdepth b e in
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:unif:out"
          [Trace_ppx_runtime.Runtime.J (Fmt.pp_print_bool, res)];
      if not res
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          ~goal_id:(Util.UUID.hash gid) "user:select"
          [Trace_ppx_runtime.Runtime.J
             (((fun fmt ->
                  fun () ->
                    let op = if matching then "match" else "unify" in
                    Fmt.fprintf fmt "@[<hov 2>fail to %s: %a@ with %a@]" op
                      (ppterm adepth [] adepth empty_env) a
                      (ppterm bdepth [] adepth e) b)), ())];
      res
    let rec deref_head ~depth  =
      function
      | UVar ({ contents = t }, from, ano) when t != C.dummy ->
          deref_head ~depth (deref_uv ~from ~to_:depth ano t)
      | AppUVar ({ contents = t }, from, args) when t != C.dummy ->
          deref_head ~depth (deref_appuv ~from ~to_:depth args t)
      | x -> x
    let full_deref ~adepth  env ~depth  t =
      let rec deref d =
        function
        | Const _ as x -> x
        | Lam r -> Lam (deref (d + 1) r)
        | App (n, x, xs) -> App (n, (deref d x), (List.map (deref d) xs))
        | Cons (hd, tl) -> Cons ((deref d hd), (deref d tl))
        | Nil as x -> x
        | Discard as x -> x
        | Arg (i, ano) when (env.(i)) != C.dummy ->
            deref d (deref_uv ~from:adepth ~to_:d ano (env.(i)))
        | Arg _ as x -> x
        | AppArg (i, args) when (env.(i)) != C.dummy ->
            deref d (deref_appuv ~from:adepth ~to_:d args (env.(i)))
        | AppArg (i, args) -> AppArg (i, (List.map (deref d) args))
        | UVar (r, lvl, ano) when (!! r) != C.dummy ->
            deref d (deref_uv ~from:lvl ~to_:d ano (!! r))
        | UVar _ as x -> x
        | AppUVar (r, lvl, args) when (!! r) != C.dummy ->
            deref d (deref_appuv ~from:lvl ~to_:d args (!! r))
        | AppUVar (r, lvl, args) ->
            AppUVar (r, lvl, (List.map (deref d) args))
        | Builtin (c, xs) -> Builtin (c, (List.map (deref d) xs))
        | CData _ as x -> x in
      deref depth t
    type assignment = (uvar_body * int * term)
    let shift_bound_vars ~depth  ~to_  t =
      let shift_db d n = if n < depth then n else (n + to_) - depth in
      let rec shift d =
        function
        | Const n as x ->
            let m = shift_db d n in if m = n then x else mkConst m
        | Lam r -> Lam (shift (d + 1) r)
        | App (n, x, xs) ->
            App ((shift_db d n), (shift d x), (List.map (shift d) xs))
        | Cons (hd, tl) -> Cons ((shift d hd), (shift d tl))
        | Nil as x -> x
        | Discard as x -> x
        | Arg _ as x -> x
        | AppArg (i, args) -> AppArg (i, (List.map (shift d) args))
        | UVar (r, _, _)|AppUVar (r, _, _) when (!! r) != C.dummy ->
            anomaly "shift_bound_vars: non-derefd term"
        | UVar _ as x -> x
        | AppUVar (r, lvl, args) ->
            AppUVar (r, lvl, (List.map (shift d) args))
        | Builtin (c, xs) -> Builtin (c, (List.map (shift d) xs))
        | CData _ as x -> x in
      if depth = to_ then t else shift depth t
    let subtract_to_consts ~amount  ~depth  t =
      let shift_db d n =
        if n < 0
        then n
        else
          if n < amount
          then error "The term cannot be put in the desired context"
          else n - amount in
      let rec shift d =
        function
        | Const n as x ->
            let m = shift_db d n in if m = n then x else mkConst m
        | Lam r -> Lam (shift (d + 1) r)
        | App (n, x, xs) ->
            App ((shift_db d n), (shift d x), (List.map (shift d) xs))
        | Cons (hd, tl) -> Cons ((shift d hd), (shift d tl))
        | Nil as x -> x
        | Discard as x -> x
        | Arg _ as x -> x
        | AppArg (i, args) -> AppArg (i, (List.map (shift d) args))
        | UVar (r, _, _)|AppUVar (r, _, _) when (!! r) != C.dummy ->
            anomaly "subtract_to_consts: non-derefd term"
        | UVar _|AppUVar _ ->
            error
              "The term cannot be put in the desired context (leftover uvar)"
        | Builtin (c, xs) -> Builtin (c, (List.map (shift d) xs))
        | CData _ as x -> x in
      if amount = 0 then t else shift 0 t
  end 
open HO
let _ = do_deref := deref_uv
let _ = do_app_deref := deref_appuv
module FFI =
  struct
    let builtins : Data.BuiltInPredicate.builtin_table ref =
      Fork.new_local (Hashtbl.create 17)
    let lookup c = Hashtbl.find (!builtins) c
    let type_err ~depth  bname n ty t =
      type_error
        ("builtin " ^
           (bname ^
              (": " ^
                 ((if n = 0 then "" else (string_of_int n) ^ "th argument: ")
                    ^
                    ("expected " ^
                       (ty ^
                          (": got " ^
                             (match t with
                              | None -> "_"
                              | Some t ->
                                  Format.asprintf "%a"
                                    (Pp.uppterm depth [] 0 empty_env) t))))))))
    let wrap_type_err bname n f x =
      try f x
      with
      | Conversion.TypeErr (ty, depth, t) ->
          type_err ~depth bname n (Conversion.show_ty_ast ty) (Some t)
    let arity_err ~depth  bname n t =
      type_error
        ("builtin " ^
           (bname ^
              (": " ^
                 (match t with
                  | None -> (string_of_int n) ^ "th argument is missing"
                  | Some t ->
                      "too many arguments at: " ^
                        (Format.asprintf "%a"
                           (Pp.uppterm depth [] 0 empty_env) t)))))
    let out_of_term ~depth  readback n bname state t =
      match deref_head ~depth t with
      | Discard -> Data.BuiltInPredicate.Discard
      | _ -> Data.BuiltInPredicate.Keep
    let in_of_term ~depth  readback n bname state t =
      wrap_type_err bname n (readback ~depth state) t
    let inout_of_term ~depth  readback n bname state t =
      wrap_type_err bname n (readback ~depth state) t
    let mk_out_assign ~depth  embed bname state input v output =
      match (output, input) with
      | (None, Data.BuiltInPredicate.Discard) -> (state, [])
      | (Some _, Data.BuiltInPredicate.Discard) -> (state, [])
      | (Some t, Data.BuiltInPredicate.Keep) ->
          let (state, t, extra) = embed ~depth state t in
          (state, (extra @ [App (Global_symbols.eqc, v, [t])]))
      | (None, Data.BuiltInPredicate.Keep) -> (state, [])
    let mk_inout_assign ~depth  embed bname state input v output =
      match output with
      | None -> (state, [])
      | Some t ->
          let (state, t, extra) =
            embed ~depth state (Data.BuiltInPredicate.Data t) in
          (state, (extra @ [App (Global_symbols.eqc, v, [t])]))
    let in_of_termC ~depth  readback n bname hyps constraints state t =
      wrap_type_err bname n (readback ~depth hyps constraints state) t
    let inout_of_termC = in_of_termC
    let mk_out_assignC ~depth  embed bname hyps constraints state input v
      output =
      match (output, input) with
      | (None, Data.BuiltInPredicate.Discard) -> (state, [])
      | (Some _, Data.BuiltInPredicate.Discard) -> (state, [])
      | (Some t, Data.BuiltInPredicate.Keep) ->
          let (state, t, extra) = embed ~depth hyps constraints state t in
          (state, (extra @ [App (Global_symbols.eqc, v, [t])]))
      | (None, Data.BuiltInPredicate.Keep) -> (state, [])
    let mk_inout_assignC ~depth  embed bname hyps constraints state input v
      output =
      match output with
      | Some t ->
          let (state, t, extra) =
            embed ~depth hyps constraints state
              (Data.BuiltInPredicate.Data t) in
          (state, (extra @ [App (Global_symbols.eqc, v, [t])]))
      | None -> (state, [])
    let map_acc f s l =
      let rec aux acc extra s =
        function
        | [] -> (s, (List.rev acc), (let open List in concat (rev extra)))
        | x::xs ->
            let (s, x, gls) = f s x in aux (x :: acc) (gls :: extra) s xs in
      aux [] [] s l
    let call (Data.BuiltInPredicate.Pred (bname, ffi, compute)) ~depth  hyps
      constraints state data =
      let rec aux : type i o h c.
        (i, o, h, c) Data.BuiltInPredicate.ffi ->
          h ->
            c ->
              compute:i ->
                reduce:(State.t -> o -> (State.t * extra_goals)) ->
                  term list ->
                    int ->
                      State.t -> extra_goals list -> (State.t * extra_goals)
        =
        fun ffi ->
          fun ctx ->
            fun constraints ->
              fun ~compute ->
                fun ~reduce ->
                  fun data ->
                    fun n ->
                      fun state ->
                        fun extra ->
                          match (ffi, data) with
                          | (Data.BuiltInPredicate.Easy _, []) ->
                              let result =
                                wrap_type_err bname 0
                                  (fun () -> compute ~depth) () in
                              let (state, l) = reduce state result in
                              (state,
                                (let open List in
                                   (concat (rev extra)) @ (rev l)))
                          | (Data.BuiltInPredicate.Read _, []) ->
                              let result =
                                wrap_type_err bname 0
                                  (compute ~depth ctx constraints) state in
                              let (state, l) = reduce state result in
                              (state,
                                (let open List in
                                   (concat (rev extra)) @ (rev l)))
                          | (Data.BuiltInPredicate.Full _, []) ->
                              let (state, result, gls) =
                                wrap_type_err bname 0
                                  (compute ~depth ctx constraints) state in
                              let (state, l) = reduce state result in
                              (state,
                                ((let open List in concat (rev extra)) @
                                   (gls @ (List.rev l))))
                          | (Data.BuiltInPredicate.VariadicIn
                             (_,
                              { ContextualConversion.readback = readback },
                              _),
                             data) ->
                              let (state, i, gls) =
                                map_acc
                                  (in_of_termC ~depth readback n bname ctx
                                     constraints) state data in
                              let (state, rest) =
                                wrap_type_err bname 0
                                  (compute i ~depth ctx constraints) state in
                              let (state, l) = reduce state rest in
                              (state,
                                (let open List in
                                   gls @ ((concat (rev extra)) @ (rev l))))
                          | (Data.BuiltInPredicate.VariadicOut
                             (_,
                              { ContextualConversion.embed = embed; readback
                                },
                              _),
                             data) ->
                              let i =
                                List.map
                                  (out_of_term ~depth readback n bname state)
                                  data in
                              let (state, (rest, out)) =
                                wrap_type_err bname 0
                                  (compute i ~depth ctx constraints) state in
                              let (state, l) = reduce state rest in
                              (match out with
                               | Some out ->
                                   let (state, ass) =
                                     map_acc3
                                       (mk_out_assignC ~depth embed bname ctx
                                          constraints) state i data out in
                                   (state,
                                     (let open List in
                                        (concat (rev extra)) @
                                          ((rev (concat ass)) @ l)))
                               | None ->
                                   (state,
                                     (let open List in
                                        (concat (rev extra)) @ (rev l))))
                          | (Data.BuiltInPredicate.VariadicInOut
                             (_,
                              { ContextualConversion.embed = embed; readback
                                },
                              _),
                             data) ->
                              let (state, i, gls) =
                                map_acc
                                  (inout_of_termC ~depth readback n bname ctx
                                     constraints) state data in
                              let (state, (rest, out)) =
                                wrap_type_err bname 0
                                  (compute i ~depth ctx constraints) state in
                              let (state, l) = reduce state rest in
                              (match out with
                               | Some out ->
                                   let (state, ass) =
                                     map_acc3
                                       (mk_inout_assignC ~depth embed bname
                                          ctx constraints) state i data out in
                                   (state,
                                     (let open List in
                                        gls @
                                          ((concat (rev extra)) @
                                             ((rev (concat ass)) @ l))))
                               | None ->
                                   (state,
                                     (let open List in
                                        gls @
                                          ((concat (rev extra)) @ (rev l)))))
                          | (Data.BuiltInPredicate.CIn
                             ({ ContextualConversion.readback = readback },
                              _, ffi),
                             t::rest) ->
                              let (state, i, gls) =
                                in_of_termC ~depth readback n bname ctx
                                  constraints state t in
                              aux ffi ctx constraints ~compute:(compute i)
                                ~reduce rest (n + 1) state (gls :: extra)
                          | (Data.BuiltInPredicate.COut
                             ({ ContextualConversion.embed = embed; readback
                                },
                              _, ffi),
                             t::rest) ->
                              let i =
                                out_of_term ~depth readback n bname state t in
                              let reduce state (rest, out) =
                                let (state, l) = reduce state rest in
                                let (state, ass) =
                                  mk_out_assignC ~depth embed bname ctx
                                    constraints state i t out in
                                (state, (ass @ l)) in
                              aux ffi ctx constraints ~compute:(compute i)
                                ~reduce rest (n + 1) state extra
                          | (Data.BuiltInPredicate.CInOut
                             ({ ContextualConversion.embed = embed; readback
                                },
                              _, ffi),
                             t::rest) ->
                              let (state, i, gls) =
                                inout_of_termC ~depth readback n bname ctx
                                  constraints state t in
                              let reduce state (rest, out) =
                                let (state, l) = reduce state rest in
                                let (state, ass) =
                                  mk_inout_assignC ~depth embed bname ctx
                                    constraints state i t out in
                                (state, (ass @ l)) in
                              aux ffi ctx constraints ~compute:(compute i)
                                ~reduce rest (n + 1) state (gls :: extra)
                          | (Data.BuiltInPredicate.In
                             ({ Conversion.readback = readback }, _, ffi),
                             t::rest) ->
                              let (state, i, gls) =
                                in_of_term ~depth readback n bname state t in
                              aux ffi ctx constraints ~compute:(compute i)
                                ~reduce rest (n + 1) state (gls :: extra)
                          | (Data.BuiltInPredicate.Out
                             ({ Conversion.embed = embed; readback }, _, ffi),
                             t::rest) ->
                              let i =
                                out_of_term ~depth readback n bname state t in
                              let reduce state (rest, out) =
                                let (state, l) = reduce state rest in
                                let (state, ass) =
                                  mk_out_assign ~depth embed bname state i t
                                    out in
                                (state, (ass @ l)) in
                              aux ffi ctx constraints ~compute:(compute i)
                                ~reduce rest (n + 1) state extra
                          | (Data.BuiltInPredicate.InOut
                             ({ Conversion.embed = embed; readback }, _, ffi),
                             t::rest) ->
                              let (state, i, gls) =
                                inout_of_term ~depth readback n bname state t in
                              let reduce state (rest, out) =
                                let (state, l) = reduce state rest in
                                let (state, ass) =
                                  mk_inout_assign ~depth embed bname state i
                                    t out in
                                (state, (ass @ l)) in
                              aux ffi ctx constraints ~compute:(compute i)
                                ~reduce rest (n + 1) state (gls :: extra)
                          | (_, t::_) -> arity_err ~depth bname n (Some t)
                          | (_, []) -> arity_err ~depth bname n None in
      let rec aux_ctx : type i o h c.
        (i, o, h, c) Data.BuiltInPredicate.ffi ->
          (h, c) ContextualConversion.ctx_readback
        =
        function
        | Data.BuiltInPredicate.Full (f, _) -> f
        | Data.BuiltInPredicate.Read (f, _) -> f
        | Data.BuiltInPredicate.VariadicIn (f, _, _) -> f
        | Data.BuiltInPredicate.VariadicOut (f, _, _) -> f
        | Data.BuiltInPredicate.VariadicInOut (f, _, _) -> f
        | Data.BuiltInPredicate.Easy _ -> ContextualConversion.unit_ctx
        | Data.BuiltInPredicate.In (_, _, rest) -> aux_ctx rest
        | Data.BuiltInPredicate.Out (_, _, rest) -> aux_ctx rest
        | Data.BuiltInPredicate.InOut (_, _, rest) -> aux_ctx rest
        | Data.BuiltInPredicate.CIn (_, _, rest) -> aux_ctx rest
        | Data.BuiltInPredicate.COut (_, _, rest) -> aux_ctx rest
        | Data.BuiltInPredicate.CInOut (_, _, rest) -> aux_ctx rest in
      let reduce state _ = (state, []) in
      let (state, ctx, csts, gls_ctx) =
        aux_ctx ffi ~depth hyps constraints state in
      let (state, gls) = aux ffi ctx csts ~compute ~reduce data 1 state [] in
      (state, (gls_ctx @ gls))
  end
let rec embed_query_aux : type a.
  mk_Arg:(State.t -> name:string -> args:term list -> (State.t * term)) ->
    depth:int ->
      predicate:constant ->
        term list ->
          term list -> State.t -> a Query.arguments -> (State.t * term)
  =
  fun ~mk_Arg ->
    fun ~depth ->
      fun ~predicate ->
        fun gls ->
          fun args ->
            fun state ->
              fun descr ->
                match descr with
                | Data.Query.D (d, x, rest) ->
                    let (state, x, glsx) = d.Conversion.embed ~depth state x in
                    embed_query_aux ~mk_Arg ~depth ~predicate (gls @ glsx) (x
                      :: args) state rest
                | Data.Query.Q (d, name, rest) ->
                    let (state, x) = mk_Arg state ~name ~args:[] in
                    embed_query_aux ~mk_Arg ~depth ~predicate gls (x :: args)
                      state rest
                | Data.Query.N ->
                    let args = List.rev args in
                    (state,
                      ((match gls with
                        | [] -> C.mkAppL predicate args
                        | gls ->
                            C.mkAppL Global_symbols.andc
                              (gls @ [C.mkAppL predicate args]))))
let embed_query ~mk_Arg  ~depth  state (Query.Query { predicate; arguments })
  = embed_query_aux ~mk_Arg ~depth ~predicate [] [] state arguments
let rec query_solution_aux : type a.
  a Query.arguments -> term StrMap.t -> State.t -> a =
  fun args ->
    fun assignments ->
      fun state ->
        match args with
        | Data.Query.N -> ()
        | Data.Query.D (_, _, args) ->
            query_solution_aux args assignments state
        | Data.Query.Q (d, name, args) ->
            let x = StrMap.find name assignments in
            let (state, x, _gls) = d.Conversion.readback ~depth:0 state x in
            (x, (query_solution_aux args assignments state))
let output arguments assignments state =
  query_solution_aux arguments assignments state
module Indexing =
  struct
    let mustbevariablec = min_int
    let ppclause f ~depth  ~hd  { args; hyps } =
      Fmt.fprintf f "@[<hov 1>%s %a :- %a.@]" (C.show hd)
        (pplist
           (uppterm ~min_prec:(Parser.appl_precedence + 1) depth [] depth
              empty_env) " ") args
        (pplist
           (uppterm ~min_prec:(Parser.appl_precedence + 1) depth [] depth
              empty_env) ", ") hyps
    let tail_opt = function | [] -> [] | _::xs -> xs
    let hd_opt = function | b::_ -> b | _ -> false
    type clause_arg_classification =
      | Variable 
      | MustBeVariable 
      | Rigid of constant * bool 
    let rec classify_clause_arg ~depth  matching t =
      match deref_head ~depth t with
      | Const k when k == Global_symbols.uvarc -> MustBeVariable
      | Const k -> Rigid (k, matching)
      | Nil -> Rigid (Global_symbols.nilc, matching)
      | Cons _ -> Rigid (Global_symbols.consc, matching)
      | App (k, _, _) when k == Global_symbols.uvarc -> MustBeVariable
      | App (k, a, _) when k == Global_symbols.asc ->
          classify_clause_arg ~depth matching a
      | App (k, _, _)|Builtin (k, _) -> Rigid (k, matching)
      | Lam _ -> Variable
      | Arg _|UVar _|AppArg _|AppUVar _|Discard -> Variable
      | CData d ->
          let hash = - (CData.hash d) in
          if hash > mustbevariablec
          then Rigid (hash, matching)
          else Rigid ((hash + 1), matching)
    let rec classify_clause_argno ~depth  argno mode =
      function
      | [] -> Variable
      | x::_ when argno == 0 -> classify_clause_arg ~depth (hd_opt mode) x
      | _::xs -> classify_clause_argno ~depth (argno - 1) (tail_opt mode) xs
    let dec_to_bin2 num =
      let rec aux x =
        if x == 1
        then ["1"]
        else
          if x == 0
          then ["0"]
          else
            if (x mod 2) == 1
            then "1" :: (aux (x / 2))
            else "0" :: (aux (x / 2)) in
      String.concat "" (List.rev (aux num))
    let hash_bits = Sys.int_size - 1
    let hash_arg_list goal hd ~depth  args mode spec =
      let nargs = let open List in length (filter (fun x -> x > 0) spec) in
      let arg_size = hash_bits / nargs in
      let hash size k =
        let modulus = 1 lsl size in
        let kabs = Hashtbl.hash k in
        let h = kabs mod modulus in
        if true
        then
          Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
            "dev:index:subhash-const"
            [Trace_ppx_runtime.Runtime.J (C.pp, k);
            Trace_ppx_runtime.Runtime.J (pp_string, (dec_to_bin2 h))];
        h in
      let all_1 size = max_int lsr (hash_bits - size) in
      let all_0 size = 0 in
      let shift slot_size position x = x lsl (slot_size * position) in
      let rec aux off acc args mode spec =
        match (args, spec) with
        | (_, []) -> acc
        | ([], _) -> acc
        | (x::xs, n::spec) ->
            let h = aux_arg arg_size (hd_opt mode) n x in
            aux (off + arg_size) (acc lor (h lsl off)) xs (tail_opt mode)
              spec
      and aux_arg size matching deep arg =
        let h =
          match deref_head ~depth arg with
          | App (k, a, _) when k == Global_symbols.asc ->
              aux_arg size matching deep a
          | Const k when k == Global_symbols.uvarc ->
              hash size mustbevariablec
          | App (k, _, _) when (k == Global_symbols.uvarc) && (deep = 1) ->
              hash size mustbevariablec
          | Const k -> hash size k
          | App (k, _, _) when deep = 1 -> hash size k
          | App (k, x, xs) ->
              let size = size / ((List.length xs) + 2) in
              let self = aux_arg size matching (deep - 1) in
              let shift = shift size in
              ((hash size k) lor (shift 1 (self x))) lor
                (let open List in
                   fold_left (lor) 0
                     (mapi (fun i -> fun x -> shift (i + 2) (self x)) xs))
          | UVar _|AppUVar _ when matching && goal ->
              hash size mustbevariablec
          | UVar _|AppUVar _ when matching -> all_1 size
          | UVar _|AppUVar _ -> if goal then all_0 size else all_1 size
          | Arg _|AppArg _ -> all_1 size
          | Nil -> hash size Global_symbols.nilc
          | Cons (x, xs) ->
              let size = size / 2 in
              let self = aux_arg size matching (deep - 1) in
              let shift = shift size in
              (hash size Global_symbols.consc) lor (shift 1 (self x))
          | CData s -> hash size (CData.hash s)
          | Lam _ -> all_1 size
          | Discard -> all_1 size
          | Builtin (k, xs) ->
              let size = size / ((List.length xs) + 1) in
              let self = aux_arg size matching (deep - 1) in
              let shift = shift size in
              (hash size k) lor
                (let open List in
                   fold_left (lor) 0
                     (mapi (fun i -> fun x -> shift (i + 1) (self x)) xs)) in
        if true
        then
          Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
            "dev:index:subhash"
            [Trace_ppx_runtime.Runtime.J
               (((fun fmt ->
                    fun () ->
                      Fmt.fprintf fmt "%s: %d: %s: %a"
                        (if goal then "goal" else "clause") size
                        (dec_to_bin2 h) (uppterm depth [] 0 empty_env) arg)),
                 ())];
        h in
      let h = aux 0 0 args mode spec in
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:index:hash"
          [Trace_ppx_runtime.Runtime.J
             (((fun fmt ->
                  fun () ->
                    Fmt.fprintf fmt "%s: %s: %a"
                      (if goal then "goal" else "clause") (dec_to_bin2 h)
                      (pplist ~boxed:true (uppterm depth [] 0 empty_env) " ")
                      ((Const hd) :: args))), ())];
      h
    let hash_clause_arg_list = hash_arg_list false
    let hash_goal_arg_list = hash_arg_list true
    let add1clause ~depth  m (predicate, clause) =
      match Ptmap.find predicate m with
      | TwoLevelIndex { all_clauses; argno; mode; flex_arg_clauses; arg_idx }
          ->
          (match classify_clause_argno ~depth argno mode clause.args with
           | Variable ->
               Ptmap.add predicate
                 (TwoLevelIndex
                    {
                      argno;
                      mode;
                      all_clauses = (clause :: all_clauses);
                      flex_arg_clauses = (clause :: flex_arg_clauses);
                      arg_idx =
                        (Ptmap.map (fun l_rev -> clause :: l_rev) arg_idx)
                    }) m
           | MustBeVariable ->
               let l_rev =
                 try Ptmap.find mustbevariablec arg_idx
                 with | Not_found -> flex_arg_clauses in
               Ptmap.add predicate
                 (TwoLevelIndex
                    {
                      argno;
                      mode;
                      all_clauses = (clause :: all_clauses);
                      flex_arg_clauses;
                      arg_idx =
                        (Ptmap.add mustbevariablec (clause :: l_rev) arg_idx)
                    }) m
           | Rigid (arg_hd, matching) ->
               let l_rev =
                 try Ptmap.find arg_hd arg_idx
                 with | Not_found -> flex_arg_clauses in
               let all_clauses =
                 if matching then all_clauses else clause :: all_clauses in
               Ptmap.add predicate
                 (TwoLevelIndex
                    {
                      argno;
                      mode;
                      all_clauses;
                      flex_arg_clauses;
                      arg_idx = (Ptmap.add arg_hd (clause :: l_rev) arg_idx)
                    }) m)
      | BitHash { mode; args; time; args_idx } ->
          let hash =
            hash_clause_arg_list predicate ~depth clause.args mode args in
          let clauses = try Ptmap.find hash args_idx with | Not_found -> [] in
          Ptmap.add predicate
            (BitHash
               {
                 mode;
                 args;
                 time = (time + 1);
                 args_idx =
                   (Ptmap.add hash ((clause, time) :: clauses) args_idx)
               }) m
      | exception Not_found ->
          (match classify_clause_argno ~depth 0 [] clause.args with
           | Variable ->
               Ptmap.add predicate
                 (TwoLevelIndex
                    {
                      argno = 0;
                      mode = [];
                      all_clauses = [clause];
                      flex_arg_clauses = [clause];
                      arg_idx = Ptmap.empty
                    }) m
           | MustBeVariable ->
               Ptmap.add predicate
                 (TwoLevelIndex
                    {
                      argno = 0;
                      mode = [];
                      all_clauses = [clause];
                      flex_arg_clauses = [];
                      arg_idx =
                        (Ptmap.add mustbevariablec [clause] Ptmap.empty)
                    }) m
           | Rigid (arg_hd, matching) ->
               let all_clauses = if matching then [] else [clause] in
               Ptmap.add predicate
                 (TwoLevelIndex
                    {
                      argno = 0;
                      mode = [];
                      all_clauses;
                      flex_arg_clauses = [];
                      arg_idx = (Ptmap.add arg_hd [clause] Ptmap.empty)
                    }) m)
    let add_clauses ~depth  clauses p =
      let p = List.fold_left (add1clause ~depth) p clauses in p
    let make_index ~depth  ~indexing  p =
      let m =
        C.Map.fold
          (fun predicate ->
             fun (mode, indexing) ->
               fun m ->
                 match indexing with
                 | Hash args ->
                     Ptmap.add predicate
                       (BitHash
                          {
                            args;
                            mode;
                            time = min_int;
                            args_idx = Ptmap.empty
                          }) m
                 | MapOn argno ->
                     Ptmap.add predicate
                       (TwoLevelIndex
                          {
                            argno;
                            mode;
                            all_clauses = [];
                            flex_arg_clauses = [];
                            arg_idx = Ptmap.empty
                          }) m) indexing Ptmap.empty in
      let p = List.rev p in { index = (add_clauses ~depth p m); src = [] }
    let add_clauses ~depth  clauses clauses_src { index; src } =
      {
        index = (add_clauses ~depth clauses index);
        src = ((List.rev clauses_src) @ src)
      }
    type goal_arg_classification =
      | Variable 
      | Rigid of constant 
    let rec classify_goal_arg ~depth  t =
      match deref_head ~depth t with
      | Const k when k == Global_symbols.uvarc -> Rigid mustbevariablec
      | Const k -> Rigid k
      | Nil -> Rigid Global_symbols.nilc
      | Cons _ -> Rigid Global_symbols.consc
      | App (k, _, _) when k == Global_symbols.uvarc -> Rigid mustbevariablec
      | App (k, a, _) when k == Global_symbols.asc ->
          classify_goal_arg ~depth a
      | App (k, _, _)|Builtin (k, _) -> Rigid k
      | Lam _ -> Variable
      | Arg _|UVar _|AppArg _|AppUVar _|Discard -> Variable
      | CData d ->
          let hash = - (CData.hash d) in
          if hash > mustbevariablec then Rigid hash else Rigid (hash + 1)
    let classify_goal_argno ~depth  argno =
      function
      | Const _ -> Variable
      | App (_, x, _) when argno == 0 -> classify_goal_arg ~depth x
      | App (_, _, xs) ->
          let x =
            try List.nth xs (argno - 1)
            with
            | Invalid_argument _ ->
                type_error "The goal is not applied enough" in
          classify_goal_arg ~depth x
      | _ -> assert false
    let hash_goal_args ~depth  mode args goal =
      match goal with
      | Const _ -> 0
      | App (k, x, xs) -> hash_goal_arg_list k ~depth (x :: xs) mode args
      | _ -> assert false
    let get_clauses ~depth  predicate goal { index = m } =
      let rc =
        try
          match Ptmap.find predicate m with
          | TwoLevelIndex
              { all_clauses; argno; mode; flex_arg_clauses; arg_idx } ->
              (match classify_goal_argno ~depth argno goal with
               | Variable -> all_clauses
               | Rigid arg_hd ->
                   (try Ptmap.find arg_hd arg_idx
                    with | Not_found -> flex_arg_clauses))
          | BitHash { args; mode; args_idx } ->
              let hash = hash_goal_args ~depth mode args goal in
              let cl = List.flatten (Ptmap.find_unifiables hash args_idx) in
              let open List in
                map fst (sort (fun (_, cl1) -> fun (_, cl2) -> cl2 - cl1) cl)
        with | Not_found -> [] in
      Trace_ppx_runtime.Runtime.log "get_clauses" (C.show predicate)
        (List.length rc);
      rc
    let rec flatten_snd =
      function | [] -> [] | (_, (hd, _, _))::tl -> hd @ (flatten_snd tl)
    let close_with_pis depth vars t =
      if vars = 0
      then t
      else
        (let fix_const c = if c < depth then c else c + vars in
         let rec aux =
           function
           | Const c -> mkConst (fix_const c)
           | Arg (i, argsno) ->
               (match C.mkinterval (depth + vars) argsno 0 with
                | [] -> Const (i + depth)
                | x::[] -> App ((i + depth), x, [])
                | x::xs -> App ((i + depth), x, xs))
           | AppArg (i, args) ->
               (match List.map aux args with
                | [] -> anomaly "AppArg to 0 args"
                | x::[] -> App ((i + depth), x, [])
                | x::xs -> App ((i + depth), x, xs))
           | App (c, x, xs) ->
               App ((fix_const c), (aux x), (List.map aux xs))
           | Builtin (c, xs) -> Builtin (c, (List.map aux xs))
           | UVar (_, _, _) as orig ->
               hmove ~from:depth ~to_:(depth + vars) orig
           | AppUVar (r, vardepth, args) -> assert false
           | Cons (hd, tl) -> Cons ((aux hd), (aux tl))
           | Nil as x -> x
           | Discard as x -> x
           | Lam t -> Lam (aux t)
           | CData _ as x -> x in
         let rec add_pis n t =
           if n = 0
           then t
           else App (Global_symbols.pic, (Lam (add_pis (n - 1) t)), []) in
         add_pis vars (aux t))
    let local_prog { src } = src
  end
open Indexing
let orig_prolog_program =
  Fork.new_local (make_index ~depth:0 ~indexing:C.Map.empty [])
module Clausify :
  sig
    val clausify :
      prolog_prog ->
        depth:int ->
          term -> ((constant * clause) list * clause_src list * int)
    val clausify1 :
      loc:Loc.t ->
        mode C.Map.t ->
          nargs:int ->
            depth:int -> term -> ((constant * clause) * clause_src * int)
    val lp_list_to_list : depth:int -> term -> term list
    val get_lambda_body : depth:int -> term -> term
    val split_conj : depth:int -> term -> term list
  end =
  struct
    let rec term_map m =
      function
      | Const x when List.mem_assoc x m -> mkConst (List.assoc x m)
      | Const _ as x -> x
      | App (c, x, xs) when List.mem_assoc c m ->
          App ((List.assoc c m), (term_map m x), (smart_map (term_map m) xs))
      | App (c, x, xs) ->
          App (c, (term_map m x), (smart_map (term_map m) xs))
      | Lam x -> Lam (term_map m x)
      | UVar _ as x -> x
      | AppUVar (r, lvl, xs) -> AppUVar (r, lvl, (smart_map (term_map m) xs))
      | Arg _ as x -> x
      | AppArg (i, xs) -> AppArg (i, (smart_map (term_map m) xs))
      | Builtin (c, xs) -> Builtin (c, (smart_map (term_map m) xs))
      | Cons (hd, tl) -> Cons ((term_map m hd), (term_map m tl))
      | Nil as x -> x
      | Discard as x -> x
      | CData _ as x -> x
    let rec split_conj ~depth  =
      function
      | App (c, hd, args) when c == Global_symbols.andc ->
          (split_conj ~depth hd) @
            (let open List in flatten (map (split_conj ~depth) args))
      | Nil -> []
      | Cons (x, xs) -> (split_conj ~depth x) @ (split_conj ~depth xs)
      | UVar ({ contents = g }, from, args) when g != C.dummy ->
          split_conj ~depth (deref_uv ~from ~to_:depth args g)
      | AppUVar ({ contents = g }, from, args) when g != C.dummy ->
          split_conj ~depth (deref_appuv ~from ~to_:depth args g)
      | Discard -> []
      | _ as f -> [f]
    let rec lp_list_to_list ~depth  =
      function
      | Cons (hd, tl) -> hd :: (lp_list_to_list ~depth tl)
      | Nil -> []
      | UVar ({ contents = g }, from, args) when g != C.dummy ->
          lp_list_to_list ~depth (deref_uv ~from ~to_:depth args g)
      | AppUVar ({ contents = g }, from, args) when g != C.dummy ->
          lp_list_to_list ~depth (deref_appuv ~from ~to_:depth args g)
      | x -> error (Fmt.sprintf "%s is not a list" (show_term x))
    let rec get_lambda_body ~depth  =
      function
      | UVar ({ contents = g }, from, args) when g != C.dummy ->
          get_lambda_body ~depth (deref_uv ~from ~to_:depth args g)
      | AppUVar ({ contents = g }, from, args) when g != C.dummy ->
          get_lambda_body ~depth (deref_appuv ~from ~to_:depth args g)
      | Lam b -> b
      | _ -> error "pi/sigma applied to something that is not a Lam"
    let rec claux1 ?loc  get_mode vars depth hyps ts lts lcs t =
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "clausify"
        (fun fmt ->
           Format.fprintf fmt "%a %d %d %d %d\n%!"
             (ppterm (depth + lts) [] 0 empty_env) t depth lts lcs
             (List.length ts));
      (try
         let rc =
           match t with
           | Discard ->
               error ?loc
                 "ill-formed hypothetical clause: discard in head position"
           | App (c, g2, g1::[]) when c == Global_symbols.rimplc ->
               claux1 ?loc get_mode vars depth ((ts, g1) :: hyps) ts lts lcs
                 g2
           | App (c, _, _) when c == Global_symbols.rimplc ->
               error ?loc "ill-formed hypothetical clause"
           | App (c, g1, g2::[]) when c == Global_symbols.implc ->
               claux1 ?loc get_mode vars depth ((ts, g1) :: hyps) ts lts lcs
                 g2
           | App (c, _, _) when c == Global_symbols.implc ->
               error ?loc "ill-formed hypothetical clause"
           | App (c, arg, []) when c == Global_symbols.sigmac ->
               let b = get_lambda_body ~depth:(depth + lts) arg in
               let args =
                 List.rev
                   (List.filter (function | Arg _ -> true | _ -> false) ts) in
               let cst =
                 match args with
                 | [] -> Const (depth + lcs)
                 | hd::rest -> App ((depth + lcs), hd, rest) in
               claux1 ?loc get_mode vars depth hyps (cst :: ts) (lts + 1)
                 (lcs + 1) b
           | App (c, arg, []) when c == Global_symbols.pic ->
               let b = get_lambda_body ~depth:(depth + lts) arg in
               claux1 ?loc get_mode (vars + 1) depth hyps ((Arg (vars, 0)) ::
                 ts) (lts + 1) lcs b
           | App (c, _, _) when c == Global_symbols.andc ->
               error ?loc
                 "Conjunction in the head of a clause is not supported"
           | Const _|App _ as g ->
               let hyps =
                 let open List in
                   flatten
                     (rev_map
                        (fun (ts, g) ->
                           let g =
                             hmove ~from:(depth + lts)
                               ~to_:((depth + lts) + lcs) g in
                           let g = subst depth ts g in
                           split_conj ~depth:(depth + lcs) g) hyps) in
               let g = hmove ~from:(depth + lts) ~to_:((depth + lts) + lcs) g in
               let g = subst depth ts g in
               let (hd, args) =
                 match g with
                 | Const h -> (h, [])
                 | App (h, x, xs) -> (h, (x :: xs))
                 | Arg _|AppArg _ -> assert false
                 | Lam _|Builtin _|CData _ -> assert false
                 | UVar _|AppUVar _ -> assert false
                 | Cons _|Nil|Discard -> assert false in
               let c =
                 {
                   depth = (depth + lcs);
                   args;
                   hyps;
                   mode = (get_mode hd);
                   vars;
                   loc
                 } in
               (if true
                then
                  Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                    "dev:claudify:extra-clause"
                    [Trace_ppx_runtime.Runtime.J
                       ((ppclause ~depth:(depth + lcs) ~hd), c)];
                ((hd, c), { hdepth = depth; hsrc = g }, lcs))
           | UVar ({ contents = g }, from, args) when g != C.dummy ->
               claux1 ?loc get_mode vars depth hyps ts lts lcs
                 (deref_uv ~from ~to_:(depth + lts) args g)
           | AppUVar ({ contents = g }, from, args) when g != C.dummy ->
               claux1 ?loc get_mode vars depth hyps ts lts lcs
                 (deref_appuv ~from ~to_:(depth + lts) args g)
           | Arg _|AppArg _ -> anomaly "claux1 called on non-heap term"
           | Builtin (c, _) ->
               raise @@ (CannotDeclareClauseForBuiltin (loc, c))
           | Lam _|CData _ as x ->
               error ?loc
                 ("Assuming a string or int or float or function:" ^
                    (show_term x))
           | UVar _|AppUVar _ -> error ?loc "Flexible hypothetical clause"
           | Nil|Cons _ -> error ?loc "ill-formed hypothetical clause" in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "clausify" false
           None elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "clausify" true
              None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "clausify"
              false (Some e) elapsed;
            raise e))
    let clausify { index } ~depth  t =
      let get_mode x =
        match Ptmap.find x index with
        | TwoLevelIndex { mode } -> mode
        | BitHash { mode } -> mode
        | exception Not_found -> [] in
      let l = split_conj ~depth t in
      let (clauses, program, lcs) =
        List.fold_left
          (fun (clauses, programs, lcs) ->
             fun t ->
               let (clause, program, lcs) =
                 try claux1 get_mode 0 depth [] [] 0 lcs t
                 with
                 | CannotDeclareClauseForBuiltin (loc, c) ->
                     error ?loc
                       ("Declaring a clause for built in predicate " ^
                          (C.show c)) in
               ((clause :: clauses), (program :: programs), lcs)) ([], [], 0)
          l in
      (clauses, program, lcs)
    let clausify1 ~loc  m ~nargs  ~depth  t =
      claux1 ~loc (fun x -> try C.Map.find x m with | Not_found -> []) nargs
        depth [] [] 0 0 t
  end 
open Clausify
type goal =
  {
  depth: int ;
  program: prolog_prog ;
  goal: term ;
  gid: UUID.t [@trace ]}
let make_subgoal_id ogid (((depth, goal))[@trace ]) =
  let gid = UUID.make () in
  if true
  then
    Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
      ~goal_id:(Util.UUID.hash ogid) "user:subgoal"
      [Trace_ppx_runtime.Runtime.J (UUID.pp, gid)];
  if true
  then
    Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
      ~goal_id:(Util.UUID.hash gid) "user:newgoal"
      [Trace_ppx_runtime.Runtime.J ((uppterm depth [] depth empty_env), goal)];
  gid[@@inline ]
let make_subgoal ((gid)[@trace ]) ~depth  program goal =
  let ((gid)[@trace ]) = make_subgoal_id gid (((depth, goal))[@trace ]) in
  { depth; program; goal; gid = ((gid)[@trace ]) }[@@inline ]
let repack_goal ((gid)[@trace ]) ~depth  program goal =
  { depth; program; goal; gid = ((gid)[@trace ]) }[@@inline ]
type frame =
  | FNil 
  | FCons of alternative * goal list * frame 
and alternative =
  {
  lvl: alternative ;
  program: prolog_prog ;
  adepth: int ;
  agoal_hd: constant ;
  ogoal_arg: term ;
  ogoal_args: term list ;
  agid: UUID.t [@trace ];
  goals: goal list ;
  stack: frame ;
  trail: T.trail ;
  state: State.t ;
  clauses: clause list ;
  next: alternative }
let noalts : alternative = Obj.magic 0
type 'x runtime =
  {
  search: unit -> alternative ;
  next_solution: alternative -> alternative ;
  destroy: unit -> unit ;
  exec: 'a 'b . ('a -> 'b) -> 'a -> 'b ;
  get: 'a . 'a Fork.local_ref -> 'a }
let do_make_runtime
  : (?max_steps:int ->
       ?delay_outside_fragment:bool -> 'x executable -> 'x runtime)
      ref
  =
  ref
    (fun ?max_steps ->
       fun ?delay_outside_fragment ->
         fun _ -> anomaly "do_make_runtime not initialized")
module Constraints :
  sig
    val propagation : unit -> constraint_def list
    val resumption : constraint_def list -> goal list
    val chrules : CHR.t Fork.local_ref
    val exect_builtin_predicate :
      constant ->
        depth:int ->
          prolog_prog -> ((UUID.t)[@trace ]) -> term list -> term list
  end =
  struct
    exception NoMatch 
    module Ice :
      sig
        type freezer
        val empty_freezer : freezer
        val freeze :
          depth:int ->
            term ->
              ground:int ->
                newground:int -> maxground:int -> freezer -> (freezer * term)
        val defrost : maxd:int -> term -> env -> to_:int -> freezer -> term
        val assignments : freezer -> assignment list
      end =
      struct
        type freezer =
          {
          c2uv: uvar_body C.Map.t ;
          uv2c: (uvar_body * term) list ;
          assignments: assignment list }
        let empty_freezer =
          { c2uv = C.Map.empty; uv2c = []; assignments = [] }
        let freeze ~depth  t ~ground  ~newground  ~maxground  f =
          let f = ref f in
          let log_assignment =
            function
            | (t, None) -> t
            | (t, Some ((r, _, nt) as s)) ->
                (f := { (!f) with assignments = (s :: ((!f).assignments)) };
                 r @:= nt;
                 t) in
          let freeze_uv r =
            try List.assq r (!f).uv2c
            with
            | Not_found ->
                let (n, c) = C.fresh_global_constant () in
                (if true
                 then
                   Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                     "dev:freeze_uv:new"
                     [Trace_ppx_runtime.Runtime.J
                        (((fun fmt ->
                             fun () ->
                               let tt = UVar (r, 0, 0) in
                               Fmt.fprintf fmt "%s == %a" (C.show n)
                                 (ppterm 0 [] 0 empty_env) tt)), ())];
                 f :=
                   {
                     (!f) with
                     c2uv = (C.Map.add n r (!f).c2uv);
                     uv2c = ((r, c) :: ((!f).uv2c))
                   };
                 c) in
          let rec faux d =
            function
            | Const _|CData _|Nil|Discard as x -> x
            | Cons (hd, tl) -> Cons ((faux d hd), (faux d tl))
            | App (c, x, xs) -> App (c, (faux d x), (List.map (faux d) xs))
            | Builtin (c, args) -> Builtin (c, (List.map (faux d) args))
            | Arg _|AppArg _ -> error "only heap terms can be frozen"
            | Lam t -> Lam (faux (d + 1) t)
            | AppUVar (r, 0, args) when (!! r) == C.dummy ->
                let args = List.map (faux d) args in
                App
                  (Global_symbols.uvarc, (freeze_uv r),
                    [list_to_lp_list args])
            | UVar (r, lvl, ano) when (!! r) == C.dummy ->
                faux d (log_assignment (expand_uv ~depth:d r ~lvl ~ano))
            | AppUVar (r, lvl, args) when (!! r) == C.dummy ->
                faux d (log_assignment (expand_appuv ~depth:d r ~lvl ~args))
            | UVar (r, lvl, ano) ->
                faux d (deref_uv ~from:lvl ~to_:d ano (!! r))
            | AppUVar (r, lvl, args) ->
                faux d (deref_appuv ~from:lvl ~to_:d args (!! r)) in
          if true
          then
            Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid) "dev:freeze:in"
              [Trace_ppx_runtime.Runtime.J
                 (((fun fmt ->
                      fun () ->
                        Fmt.fprintf fmt
                          "depth:%d ground:%d newground:%d maxground:%d %a"
                          depth ground newground maxground
                          (uppterm depth [] 0 empty_env) t)), ())];
          (let t = faux depth t in
           if true
           then
             Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
               "dev:freeze:after-faux"
               [Trace_ppx_runtime.Runtime.J
                  ((uppterm depth [] 0 empty_env), t)];
           (let t = shift_bound_vars ~depth ~to_:ground t in
            if true
            then
              Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                "dev:freeze:after-shift->ground"
                [Trace_ppx_runtime.Runtime.J
                   ((uppterm ground [] 0 empty_env), t)];
            (let t = shift_bound_vars ~depth:0 ~to_:(newground - ground) t in
             if true
             then
               Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                 "dev:freeze:after-reloc->newground"
                 [Trace_ppx_runtime.Runtime.J
                    ((uppterm newground [] 0 empty_env), t)];
             (let t = shift_bound_vars ~depth:newground ~to_:maxground t in
              if true
              then
                Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                  "dev:freeze:out"
                  [Trace_ppx_runtime.Runtime.J
                     ((uppterm maxground [] 0 empty_env), t)];
              ((!f), t)))))
        let defrost ~maxd  t env ~to_  f =
          if true
          then
            Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
              "dev:defrost:in"
              [Trace_ppx_runtime.Runtime.J
                 (((fun fmt ->
                      fun () ->
                        Fmt.fprintf fmt "maxd:%d to:%d %a" maxd to_
                          (uppterm maxd [] maxd env) t)), ())];
          (let t = full_deref ~adepth:maxd env ~depth:maxd t in
           if true
           then
             Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
               "dev:defrost:fully-derefd"
               [Trace_ppx_runtime.Runtime.J
                  (((fun fmt ->
                       fun () ->
                         Fmt.fprintf fmt "maxd:%d to:%d %a" maxd to_
                           (uppterm maxd [] 0 empty_env) t)), ())];
           (let t = subtract_to_consts ~amount:(maxd - to_) ~depth:maxd t in
            if true
            then
              Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                "dev:defrost:shifted"
                [Trace_ppx_runtime.Runtime.J
                   (((fun fmt ->
                        fun () ->
                          Fmt.fprintf fmt "maxd:%d to:%d %a" maxd to_
                            (uppterm to_ [] 0 empty_env) t)), ())];
            (let rec daux d =
               function
               | Const c when C.Map.mem c f.c2uv ->
                   UVar ((C.Map.find c f.c2uv), 0, 0)
               | Const _|CData _|Nil|Discard as x -> x
               | Cons (hd, tl) -> Cons ((daux d hd), (daux d tl))
               | App (c, Const x, args::[]) when c == Global_symbols.uvarc ->
                   let r = C.Map.find x f.c2uv in
                   let args = lp_list_to_list ~depth:d args in
                   mkAppUVar r 0 (List.map (daux d) args)
               | App (c, x, xs) ->
                   App (c, (daux d x), (List.map (daux d) xs))
               | Builtin (c, args) -> Builtin (c, (List.map (daux d) args))
               | Arg (i, ano) when (env.(i)) != C.dummy ->
                   daux d (deref_uv ~from:to_ ~to_:d ano (env.(i)))
               | AppArg (i, args) when (env.(i)) != C.dummy ->
                   daux d (deref_appuv ~from:to_ ~to_:d args (env.(i)))
               | Arg (i, _)|AppArg (i, _) as x ->
                   (env.(i) <- (UVar ((oref C.dummy), to_, 0)); daux d x)
               | Lam t -> Lam (daux (d + 1) t)
               | UVar _ as x -> x
               | AppUVar (r, lvl, args) ->
                   AppUVar (r, lvl, (List.map (daux d) args)) in
             daux to_ t)))
        let assignments { assignments } = assignments
        let replace_const m t =
          let rec rcaux =
            function
            | Const c as x ->
                (try mkConst (List.assoc c m) with | Not_found -> x)
            | Lam t -> Lam (rcaux t)
            | App (c, x, xs) ->
                App
                  (((try List.assoc c m with | Not_found -> c)), (rcaux x),
                    (smart_map rcaux xs))
            | Builtin (c, xs) -> Builtin (c, (smart_map rcaux xs))
            | Cons (hd, tl) -> Cons ((rcaux hd), (rcaux tl))
            | CData _|UVar _|Nil|Discard as x -> x
            | Arg _|AppArg _ -> assert false
            | AppUVar (r, lvl, args) ->
                AppUVar (r, lvl, (smart_map rcaux args)) in
          if true
          then
            Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
              "dev:replace_const:in"
              [Trace_ppx_runtime.Runtime.J ((uppterm 0 [] 0 empty_env), t)];
          (let t = rcaux t in
           if true
           then
             Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
               "dev:replace_const:out"
               [Trace_ppx_runtime.Runtime.J ((uppterm 0 [] 0 empty_env), t)];
           t)
        let ppmap fmt (g, l) =
          let aux fmt (c1, c2) =
            Fmt.fprintf fmt "%s -> %s" (C.show c1) (C.show c2) in
          Fmt.fprintf fmt "%d = %a" g (pplist aux ",") l
      end 
    let match_goal ((gid)[@trace ]) goalno maxground env freezer
      (newground, depth, t) pattern =
      let (freezer, t) =
        Ice.freeze ~depth t ~ground:depth ~newground ~maxground freezer in
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "match_goal"
        (fun fmt ->
           Format.fprintf fmt "@[<hov>%a ===@ %a@]"
             (uppterm maxground [] maxground env) t
             (uppterm 0 [] maxground env) pattern);
      (try
         let rc =
           if unif ~matching:false ((gid)[@trace ]) maxground env 0 t pattern
           then freezer
           else raise NoMatch in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "match_goal" false
           None elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "match_goal"
              true None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "match_goal"
              false (Some e) elapsed;
            raise e))
    let match_context ((gid)[@trace ]) goalno maxground env freezer
      (newground, ground, lt) pattern =
      let (freezer, lt) =
        map_acc
          (fun freezer ->
             fun { hdepth = depth; hsrc = t } ->
               Ice.freeze ~depth t ~ground ~newground ~maxground freezer)
          freezer lt in
      let t = list_to_lp_list lt in
      let wall_clock = Unix.gettimeofday () in
      Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "match_context"
        (fun fmt ->
           Format.fprintf fmt "@[<hov>%a ===@ %a@]"
             (uppterm maxground [] maxground env) t
             (uppterm 0 [] maxground env) pattern);
      (try
         let rc =
           if unif ~matching:false ((gid)[@trace ]) maxground env 0 t pattern
           then freezer
           else raise NoMatch in
         let elapsed = (Unix.gettimeofday ()) -. wall_clock in
         Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "match_context"
           false None elapsed;
         rc
       with
       | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "match_context"
              true None elapsed;
            Obj.obj f (Obj.obj x))
       | e ->
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "match_context"
              false (Some e) elapsed;
            raise e))
    type chrattempt =
      {
      propagation_rule: CHR.rule ;
      constraints: constraint_def list }
    module HISTORY =
      (Hashtbl.Make)(struct
                       type t = chrattempt
                       let hash = Hashtbl.hash
                       let equal { propagation_rule = p; constraints = lp }
                         { propagation_rule = p'; constraints = lp' } =
                         (p == p') && (for_all2 (==) lp lp')
                     end)
    let chrules = Fork.new_local CHR.empty
    let make_constraint_def ~rid  ~gid:((gid)[@trace ])  depth prog pdiff
      conclusion =
      {
        cdepth = depth;
        prog;
        context = pdiff;
        cgid = ((gid)[@trace ]);
        conclusion
      }
    let delay_goal ?(filter_ctx= fun _ -> true)  ~depth  prog ~goal:g 
      ((gid)[@trace ]) ~on:keys  =
      let pdiff = local_prog prog in
      let pdiff = List.filter filter_ctx pdiff in
      if true
      then
        Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
          ~goal_id:(Util.UUID.hash gid) "user:suspend"
          [Trace_ppx_runtime.Runtime.J ((uppterm depth [] 0 empty_env), g)];
      (let kind =
         Constraint
           (make_constraint_def ~rid ~gid:((gid)[@trace ]) depth prog pdiff g) in
       CS.declare_new { kind; blockers = keys })
    let rec head_of =
      function
      | Const x -> x
      | App (x, Lam f, _) when x == Global_symbols.pic -> head_of f
      | App (x, hd, _) when x == Global_symbols.rimplc -> head_of hd
      | App (x, hd, _) when x == Global_symbols.andc -> head_of hd
      | App (x, _, _) -> x
      | Builtin (x, _) -> x
      | AppUVar (r, _, _)|UVar (r, _, _) when (!! r) != C.dummy ->
          head_of (!! r)
      | CData _ -> type_error "A constraint cannot be a primitive data"
      | Cons (x, _) -> head_of x
      | Nil -> type_error "A constraint cannot be a list"
      | UVar _|AppUVar _ ->
          type_error "A constraint cannot have flexible head"
      | Arg _|AppArg _ -> anomaly "head_of on non-heap term"
      | Discard -> type_error "A constraint cannot be _"
      | Lam _ -> type_error "A constraint cannot be a function"
    let dummy_uvar_body = { contents = C.dummy; rest = [] }
    let declare_constraint ~depth  prog ((gid)[@trace ]) args =
      let (g, keys) =
        match args with
        | t1::t2::[] ->
            let err =
              "the second argument of declare_constraint must be a list of variables" in
            let rec collect_keys t =
              match deref_head ~depth t with
              | UVar (r, _, _)|AppUVar (r, _, _) -> [r]
              | Discard -> [dummy_uvar_body]
              | _ -> type_error err
            and collect_keys_list t =
              match deref_head ~depth t with
              | Nil -> []
              | Cons (hd, tl) -> (collect_keys hd) @ (collect_keys_list tl)
              | _ -> type_error err in
            (t1, (collect_keys_list t2))
        | _ -> type_error "declare_constraint takes 2 arguments" in
      match CHR.clique_of (head_of g) (!chrules) with
      | Some clique ->
          delay_goal
            ~filter_ctx:(fun { hsrc = x } -> C.Set.mem (head_of x) clique)
            ~depth prog ~goal:g ((gid)[@trace ]) ~on:keys
      | None -> delay_goal ~depth prog ~goal:g ((gid)[@trace ]) ~on:keys
    let exect_builtin_predicate c ~depth  idx ((gid)[@trace ]) args =
      if c == Global_symbols.declare_constraintc
      then (declare_constraint ~depth idx ((gid)[@trace ]) args; [])
      else
        if c == Global_symbols.print_constraintsc
        then
          (printf "@[<hov 0>%a@]\n%!" (CS.print ?pp_ctx:None)
             (CS.contents ());
           [])
        else
          (let b =
             try FFI.lookup c
             with
             | Not_found ->
                 anomaly ("no built-in predicated named " ^ (C.show c)) in
           let constraints = !CS.Ugly.delayed in
           let state = !CS.state in
           let (state, gs) =
             FFI.call b ~depth (local_prog idx) constraints state args in
           CS.state := state; gs)
    let match_head { conclusion = x; cdepth } p =
      match deref_head ~depth:cdepth x with
      | Const x -> x == p
      | App (x, _, _) -> x == p
      | _ -> false
    let try_fire_rule ((gid)[@trace ]) rule (constraints as orig_constraints)
      =
      let { CHR.to_match = pats_to_match; to_remove = pats_to_remove; 
            patsno; new_goal; guard; nargs; pattern = quick_filter; rule_name
            }
        = rule in
      if patsno < 1
      then error "CHR propagation must mention at least one constraint";
      if not (List.for_all2 match_head constraints quick_filter)
      then None
      else
        (let (max_depth, constraints) =
           let (max_depth, constraints) =
             List.fold_left
               (fun (md, res) ->
                  fun c -> let md = md + c.cdepth in (md, ((md, c) :: res)))
               (0, []) constraints in
           (max_depth, (List.rev constraints)) in
         let (constraints_depts, constraints_contexts, constraints_goals) =
           List.fold_right
             (fun (dto, { context = c; cdepth = d; conclusion = g }) ->
                fun (ds, ctxs, gs) ->
                  (((dto, d, d) :: ds), ((dto, d, c) :: ctxs), ((dto, d, g)
                    :: gs))) constraints ([], [], []) in
         let env = Array.make nargs C.dummy in
         let (patterns_eigens, patterns_contexts, patterns_goals) =
           List.fold_right
             (fun { CHR.eigen = eigen; context; conclusion } ->
                fun (es, cs, gs) ->
                  ((eigen :: es), (context :: cs), (conclusion :: gs)))
             (pats_to_match @ pats_to_remove) ([], [], []) in
         let match_eigen i m (dto, d, eigen) pat =
           match_goal ((gid)[@trace ]) i max_depth env m
             (dto, d, (Data.C.of_int eigen)) pat in
         let match_conclusion i m g pat =
           match_goal ((gid)[@trace ]) i max_depth env m g pat in
         let match_context i m ctx pctx =
           match_context ((gid)[@trace ]) i max_depth env m ctx pctx in
         let guard =
           match guard with
           | Some g -> g
           | None -> mkConst Global_symbols.truec in
         let initial_program = !orig_prolog_program in
         let executable =
           {
             compiled_program = initial_program;
             chr = CHR.empty;
             initial_goal =
               (move ~adepth:max_depth ~from:max_depth ~to_:max_depth env
                  (shift_bound_vars ~depth:0 ~to_:max_depth guard));
             assignments = StrMap.empty;
             initial_depth = max_depth;
             initial_runtime_state =
               (let open State in
                  (((init ()) |> State.begin_goal_compilation) |>
                     (end_goal_compilation StrMap.empty))
                    |> end_compilation);
             query_arguments = Query.N;
             symbol_table = (!C.table);
             builtins = (!FFI.builtins)
           } in
         let { search; get; exec; destroy } = (!do_make_runtime) executable in
         let check_guard () =
           try
             let _ = search () in
             if (get CS.Ugly.delayed) <> []
             then error "propagation rules must declare constraint(s)"
           with | No_clause -> raise NoMatch in
         let result =
           try
             let m =
               exec
                 (fun m ->
                    if true
                    then
                      Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                        "dev:CHR:candidate"
                        [Trace_ppx_runtime.Runtime.J
                           ((pplist
                               (fun f ->
                                  fun x ->
                                    let (dto, dt, t) = x in
                                    Format.fprintf f
                                      "(lives-at:%d, to-be-lifted-to:%d) %a"
                                      dt dto (uppterm dt [] 0 empty_env) t)
                               ";"), constraints_goals)];
                    (let m =
                       fold_left2i match_eigen m constraints_depts
                         patterns_eigens in
                     let m =
                       fold_left2i match_conclusion m constraints_goals
                         patterns_goals in
                     let m =
                       fold_left2i match_context m constraints_contexts
                         patterns_contexts in
                     if true
                     then
                       Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                         "dev:CHR:matching-assignments"
                         [Trace_ppx_runtime.Runtime.J
                            ((pplist (uppterm max_depth [] 0 empty_env)
                                ~boxed:false ","), (Array.to_list env))];
                     T.to_resume := [];
                     assert ((!T.new_delayed) = []);
                     m)) Ice.empty_freezer in
             if true
             then
               Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                 "dev:CHR:maxdepth"
                 [Trace_ppx_runtime.Runtime.J (Fmt.pp_print_int, max_depth)];
             check_guard ();
             (let (_, constraints_to_remove) =
                let len_pats_to_match = List.length pats_to_match in
                partition_i (fun i -> fun _ -> i < len_pats_to_match)
                  orig_constraints in
              let new_goals =
                match new_goal with
                | None -> None
                | Some { CHR.eigen = eigen; context; conclusion } ->
                    let eigen =
                      match full_deref ~adepth:max_depth env ~depth:max_depth
                              eigen
                      with
                      | CData x when Data.C.is_int x -> Data.C.to_int x
                      | Discard -> max_depth
                      | _ -> error "eigen not resolving to an integer" in
                    let conclusion =
                      Ice.defrost ~maxd:max_depth ~to_:eigen
                        (App (Global_symbols.implc, context, [conclusion]))
                        env m in
                    let prog = initial_program in
                    Some
                      (make_constraint_def ~rid
                         ~gid:((make_subgoal_id gid (eigen, conclusion))
                         [@trace ]) eigen prog [] conclusion) in
              if true
              then
                Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                  "dev:CHR:try-rule:success" [];
              Some
                (rule_name, constraints_to_remove, new_goals,
                  (Ice.assignments m)))
           with
           | NoMatch ->
               (if true
                then
                  Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                    "dev:CHR:try-rule:fail" [];
                None) in
         destroy (); result)
    let resumption to_be_resumed_rev =
      List.map
        (fun { cdepth = d; prog; conclusion = g; cgid = ((gid)[@trace ]) } ->
           if true
           then
             Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
               ~goal_id:(Util.UUID.hash gid) "user:resume"
               [Trace_ppx_runtime.Runtime.J ((uppterm d [] d empty_env), g)];
           ((repack_goal)[@inlined ]) ~depth:d ((gid)[@trace ]) prog g)
        (List.rev to_be_resumed_rev)
    let mk_permutations len pivot pivot_position rest =
      let open List in
        let rec insert x =
          function
          | [] -> [[x]]
          | hd::tl as l -> (x :: l) :: (map (fun y -> hd :: y) (insert x tl)) in
        let rec aux n l =
          if n = 0
          then [[]]
          else
            (match l with
             | [] -> []
             | hd::tl when hd == pivot -> aux n tl
             | hd::tl ->
                 (flatten (map (insert hd) (aux (n - 1) tl))) @ (aux n tl)) in
        let permutations_no_pivot = aux (len - 1) rest in
        permutations_no_pivot |>
          (map
             (fun l ->
                let (before, after) =
                  partition_i (fun i -> fun _ -> i < pivot_position) l in
                before @ (pivot :: after)))
    let propagation () =
      let to_be_resumed_rev = ref [] in
      let removed = ref [] in
      let outdated cs = List.exists (fun x -> List.memq x (!removed)) cs in
      while (!CS.new_delayed) <> [] do
        (match !CS.new_delayed with
         | [] -> anomaly "Empty list"
         | { CS.cstr = active; cstr_blockers = overlapping }::rest ->
             (CS.new_delayed := rest;
              (let rules =
                 CHR.rules_for (head_of active.conclusion) (!chrules) in
               rules |>
                 (List.iter
                    (fun rule ->
                       for position = 0 to rule.CHR.patsno - 1 do
                         if
                           not
                             (match_head active
                                (List.nth rule.CHR.pattern position))
                         then ()
                         else
                           (let permutations =
                              mk_permutations rule.CHR.patsno active position
                                (List.map fst (CS.contents ~overlapping ())) in
                            permutations |>
                              (List.iter
                                 (fun constraints ->
                                    if outdated constraints
                                    then ()
                                    else
                                      (if true
                                       then
                                         Trace_ppx_runtime.Runtime.info
                                           ~runtime_id:(!rid)
                                           ~goal_id:(Util.UUID.hash
                                                       active.cgid)
                                           "user:CHR:try-rule-on"
                                           [Trace_ppx_runtime.Runtime.J
                                              (UUID.pp, (active.cgid))];
                                       (match try_fire_rule ((active.cgid)
                                                [@trace ]) rule constraints
                                        with
                                        | None ->
                                            if true
                                            then
                                              Trace_ppx_runtime.Runtime.info
                                                ~runtime_id:(!rid)
                                                "user:CHR:rule-failed" []
                                        | Some
                                            (rule_name, to_be_removed,
                                             to_be_added, assignments)
                                            ->
                                            (if true
                                             then
                                               Trace_ppx_runtime.Runtime.info
                                                 ~runtime_id:(!rid)
                                                 ~goal_id:(Util.UUID.hash
                                                             ((active.cgid)
                                                             [@trace ]))
                                                 "user:CHR:rule-fired"
                                                 [Trace_ppx_runtime.Runtime.J
                                                    (pp_string, rule_name)];
                                             if true
                                             then
                                               Trace_ppx_runtime.Runtime.info
                                                 ~runtime_id:(!rid)
                                                 ~goal_id:(Util.UUID.hash
                                                             ((active.cgid)
                                                             [@trace ]))
                                                 "user:CHR:rule-remove-constraints"
                                                 ((List.map
                                                     (fun x ->
                                                        Trace_ppx_runtime.Runtime.J
                                                          ((fun fmt ->
                                                              fun { cgid } ->
                                                                UUID.pp fmt
                                                                  cgid), x))
                                                     to_be_removed)
                                                    @ []);
                                             removed :=
                                               (to_be_removed @ (!removed));
                                             List.iter
                                               CS.remove_old_constraint
                                               to_be_removed;
                                             List.iter
                                               (fun (r, _lvl, t) -> r @:= t)
                                               assignments;
                                             (match to_be_added with
                                              | None -> ()
                                              | Some to_be_added ->
                                                  to_be_resumed_rev :=
                                                    (to_be_added ::
                                                    (!to_be_resumed_rev)))))))))
                       done)))))
        done;
      !to_be_resumed_rev
  end 
module Mainloop :
  sig
    val make_runtime :
      ?max_steps:int ->
        ?delay_outside_fragment:bool -> 'x executable -> 'x runtime
  end =
  struct
    let steps_bound = Fork.new_local None
    let steps_made = Fork.new_local 0
    let pred_of g =
      match g with
      | App (c, _, _) -> Some (C.show c)
      | Const c -> Some (C.show c)
      | Builtin (c, _) -> Some (C.show c)
      | _ -> None
    let pp_candidate ~depth  ~k  fmt ({ loc } as cl) =
      match loc with
      | Some x -> Util.CData.pp fmt (Ast.cloc.Util.CData.cin x)
      | None ->
          Fmt.fprintf fmt "hypothetical clause: %a" (ppclause ~depth ~hd:k)
            cl
    let make_runtime
      : ?max_steps:int ->
          ?delay_outside_fragment:bool -> 'x executable -> 'x runtime
      =
      let rec run depth p g ((gid)[@trace ]) gs (next : frame) alts lvl =
        Trace_ppx_runtime.Runtime.set_cur_pred (pred_of g);
        (let wall_clock = Unix.gettimeofday () in
         Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "run"
           (fun _ -> ());
         (try
            let rc =
              (match !steps_bound with
               | Some bound ->
                   (incr steps_made;
                    if (!steps_made) > bound then raise No_more_steps)
               | None -> ());
              (match resume_all () with
               | None ->
                   (if true
                    then
                      Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                        ~goal_id:(Util.UUID.hash gid) "user:rule"
                        [Trace_ppx_runtime.Runtime.J
                           (pp_string, "fail-resume")];
                    raise
                      (Trace_ppx_runtime.Runtime.TREC_CALL
                         ((Obj.repr next_alt), (Obj.repr alts))))
               | Some
                   ({ depth = ndepth; program; goal; gid = ((ngid)[@trace ])
                      }::goals)
                   ->
                   (if true
                    then
                      Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                        ~goal_id:(Util.UUID.hash gid) "user:rule"
                        [Trace_ppx_runtime.Runtime.J (pp_string, "resume")];
                    raise
                      (Trace_ppx_runtime.Runtime.TREC_CALL
                         ((Obj.repr
                             (run ndepth program goal ((ngid)[@trace ])
                                (goals @
                                   ((((repack_goal)[@inlined ]) ((gid)
                                       [@trace ]) ~depth p g)
                                   :: gs)) next alts)), (Obj.repr lvl))))
               | Some [] ->
                   (if true
                    then
                      Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                        ~goal_id:(Util.UUID.hash gid) "user:curgoal"
                        [Trace_ppx_runtime.Runtime.J
                           ((uppterm depth [] 0 empty_env), g)];
                    (match g with
                     | Builtin (c, []) when c == Global_symbols.cutc ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J (pp_string, "cut")];
                          raise
                            (Trace_ppx_runtime.Runtime.TREC_CALL
                               ((Obj.repr (cut ((gid)[@trace ]) gs next alts)),
                                 (Obj.repr lvl))))
                     | App (c, g, gs') when c == Global_symbols.andc ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J (pp_string, "and")];
                          (let gs' =
                             List.map
                               (fun x ->
                                  ((make_subgoal)[@inlined ]) ~depth ((gid)
                                    [@trace ]) p x) gs' in
                           let ((gid)[@trace ]) =
                             make_subgoal_id gid (((depth, g))[@trace ]) in
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (run depth p g ((gid)[@trace ])
                                       (gs' @ gs) next alts)),
                                  (Obj.repr lvl)))))
                     | Cons (g, gs') ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J (pp_string, "and")];
                          (let gs' =
                             ((make_subgoal)[@inlined ]) ~depth ((gid)
                               [@trace ]) p gs' in
                           let ((gid)[@trace ]) =
                             make_subgoal_id gid (((depth, g))[@trace ]) in
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (run depth p g ((gid)[@trace ]) (gs' ::
                                       gs) next alts)), (Obj.repr lvl)))))
                     | Nil ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "true")];
                          (match gs with
                           | [] ->
                               raise
                                 (Trace_ppx_runtime.Runtime.TREC_CALL
                                    ((Obj.repr (pop_andl alts next)),
                                      (Obj.repr lvl)))
                           | { depth; program; goal; gid = ((gid)[@trace ]) }::gs
                               ->
                               raise
                                 (Trace_ppx_runtime.Runtime.TREC_CALL
                                    ((Obj.repr
                                        (run depth program goal ((gid)
                                           [@trace ]) gs next alts)),
                                      (Obj.repr lvl)))))
                     | App (c, g2, g1::[]) when c == Global_symbols.rimplc ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "implication")];
                          (let (clauses, pdiff, lcs) = clausify p ~depth g1 in
                           let g2 = hmove ~from:depth ~to_:(depth + lcs) g2 in
                           let ((gid)[@trace ]) =
                             make_subgoal_id gid (((depth, g2))[@trace ]) in
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (run (depth + lcs)
                                       (add_clauses ~depth clauses pdiff p)
                                       g2 ((gid)[@trace ]) gs next alts)),
                                  (Obj.repr lvl)))))
                     | App (c, g1, g2::[]) when c == Global_symbols.implc ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "implication")];
                          (let (clauses, pdiff, lcs) = clausify p ~depth g1 in
                           let g2 = hmove ~from:depth ~to_:(depth + lcs) g2 in
                           let ((gid)[@trace ]) =
                             make_subgoal_id gid (((depth, g2))[@trace ]) in
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (run (depth + lcs)
                                       (add_clauses ~depth clauses pdiff p)
                                       g2 ((gid)[@trace ]) gs next alts)),
                                  (Obj.repr lvl)))))
                     | App (c, arg, []) when c == Global_symbols.pic ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J (pp_string, "pi")];
                          (let f = get_lambda_body ~depth arg in
                           let ((gid)[@trace ]) =
                             make_subgoal_id gid ((((depth + 1), f))
                               [@trace ]) in
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (run (depth + 1) p f ((gid)[@trace ]) gs
                                       next alts)), (Obj.repr lvl)))))
                     | App (c, arg, []) when c == Global_symbols.sigmac ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "sigma")];
                          (let f = get_lambda_body ~depth arg in
                           let v = UVar ((oref C.dummy), depth, 0) in
                           let fv = subst depth [v] f in
                           let ((gid)[@trace ]) =
                             make_subgoal_id gid (((depth, fv))[@trace ]) in
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (run depth p fv ((gid)[@trace ]) gs next
                                       alts)), (Obj.repr lvl)))))
                     | UVar ({ contents = g }, from, args) when g != C.dummy
                         ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "deref")];
                          raise
                            (Trace_ppx_runtime.Runtime.TREC_CALL
                               ((Obj.repr
                                   (run depth p
                                      (deref_uv ~from ~to_:depth args g)
                                      ((gid)[@trace ]) gs next alts)),
                                 (Obj.repr lvl))))
                     | AppUVar ({ contents = t }, from, args) when
                         t != C.dummy ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "deref")];
                          raise
                            (Trace_ppx_runtime.Runtime.TREC_CALL
                               ((Obj.repr
                                   (run depth p
                                      (deref_appuv ~from ~to_:depth args t)
                                      ((gid)[@trace ]) gs next alts)),
                                 (Obj.repr lvl))))
                     | Const k ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "backchain")];
                          (let clauses = get_clauses depth k g p in
                           if true
                           then
                             Trace_ppx_runtime.Runtime.info
                               ~runtime_id:(!rid)
                               ~goal_id:(Util.UUID.hash gid)
                               "user:candidates"
                               ((List.map
                                   (fun x ->
                                      Trace_ppx_runtime.Runtime.J
                                        ((pp_candidate ~depth ~k), x))
                                   clauses)
                                  @ []);
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (backchain depth p (k, C.dummy, [], gs)
                                       ((gid)[@trace ]) next alts lvl)),
                                  (Obj.repr clauses)))))
                     | App (k, x, xs) ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "backchain")];
                          (let clauses = get_clauses depth k g p in
                           if true
                           then
                             Trace_ppx_runtime.Runtime.info
                               ~runtime_id:(!rid)
                               ~goal_id:(Util.UUID.hash gid)
                               "user:candidates"
                               ((List.map
                                   (fun x ->
                                      Trace_ppx_runtime.Runtime.J
                                        ((pp_candidate ~depth ~k), x))
                                   clauses)
                                  @ []);
                           raise
                             (Trace_ppx_runtime.Runtime.TREC_CALL
                                ((Obj.repr
                                    (backchain depth p (k, x, xs, gs) ((gid)
                                       [@trace ]) next alts lvl)),
                                  (Obj.repr clauses)))))
                     | Builtin (c, args) ->
                         (if true
                          then
                            Trace_ppx_runtime.Runtime.info ~runtime_id:(
                              !rid) ~goal_id:(Util.UUID.hash gid) "user:rule"
                              [Trace_ppx_runtime.Runtime.J
                                 (pp_string, "builtin")];
                          (match Constraints.exect_builtin_predicate c ~depth
                                   p ((gid)[@trace ]) args
                           with
                           | gs' ->
                               (if true
                                then
                                  Trace_ppx_runtime.Runtime.info
                                    ~runtime_id:(!rid)
                                    ~goal_id:(Util.UUID.hash gid)
                                    "user:builtin"
                                    [Trace_ppx_runtime.Runtime.J
                                       (pp_string, "success")];
                                (match (List.map
                                          (fun g ->
                                             ((make_subgoal)[@inlined ])
                                               ((gid)[@trace ]) ~depth p g)
                                          gs')
                                         @ gs
                                 with
                                 | [] ->
                                     raise
                                       (Trace_ppx_runtime.Runtime.TREC_CALL
                                          ((Obj.repr (pop_andl alts next)),
                                            (Obj.repr lvl)))
                                 | { depth; program; goal;
                                     gid = ((gid)[@trace ]) }::gs ->
                                     raise
                                       (Trace_ppx_runtime.Runtime.TREC_CALL
                                          ((Obj.repr
                                              (run depth program goal ((gid)
                                                 [@trace ]) gs next alts)),
                                            (Obj.repr lvl)))))
                           | exception No_clause ->
                               (if true
                                then
                                  Trace_ppx_runtime.Runtime.info
                                    ~runtime_id:(!rid)
                                    ~goal_id:(Util.UUID.hash gid)
                                    "user:builtin"
                                    [Trace_ppx_runtime.Runtime.J
                                       (pp_string, "fail")];
                                raise
                                  (Trace_ppx_runtime.Runtime.TREC_CALL
                                     ((Obj.repr next_alt), (Obj.repr alts))))))
                     | Arg _|AppArg _ ->
                         anomaly "The goal is not a heap term"
                     | Lam _|CData _ ->
                         type_error
                           ("The goal is not a predicate:" ^ (show_term g))
                     | UVar _|AppUVar _|Discard ->
                         error "The goal is a flexible term"))) in
            let elapsed = (Unix.gettimeofday ()) -. wall_clock in
            Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "run" false
              None elapsed;
            rc
          with
          | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
              let elapsed = (Unix.gettimeofday ()) -. wall_clock in
              (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "run" true
                 None elapsed;
               Obj.obj f (Obj.obj x))
          | e ->
              let elapsed = (Unix.gettimeofday ()) -. wall_clock in
              (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "run" false
                 (Some e) elapsed;
               raise e)))
      and backchain depth p (k, arg, args_of_g, gs) ((gid)[@trace ]) next
        alts lvl cp =
        let wall_clock = Unix.gettimeofday () in
        Trace_ppx_runtime.Runtime.enter ~runtime_id:(!rid) "select"
          (fun _ -> ());
        (try
           let rc =
             match cp with
             | [] ->
                 (if true
                  then
                    Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                      ~goal_id:(Util.UUID.hash gid) "user:select"
                      [Trace_ppx_runtime.Runtime.J (pp_string, "fail")];
                  raise
                    (Trace_ppx_runtime.Runtime.TREC_CALL
                       ((Obj.repr next_alt), (Obj.repr alts))))
             | { depth = c_depth; mode = c_mode; args = c_args;
                 hyps = c_hyps; vars = c_vars; loc }::cs ->
                 (if true
                  then
                    Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                      ~goal_id:(Util.UUID.hash gid) "user:select"
                      [Trace_ppx_runtime.Runtime.J
                         ((pp_option Util.CData.pp),
                           (Util.option_map Ast.cloc.Util.CData.cin loc));
                      Trace_ppx_runtime.Runtime.J
                        ((ppclause ~depth ~hd:k),
                          {
                            depth = c_depth;
                            mode = c_mode;
                            args = c_args;
                            hyps = c_hyps;
                            vars = c_vars;
                            loc
                          })];
                  (let old_trail = !T.trail in
                   T.last_call := ((alts == noalts) && (cs == []));
                   (let env = Array.make c_vars C.dummy in
                    match match c_args with
                          | [] -> (arg == C.dummy) && (args_of_g == [])
                          | x::xs ->
                              (arg != C.dummy) &&
                                ((match c_mode with
                                  | [] ->
                                      (unif ~matching:false ((gid)[@trace ])
                                         depth env c_depth arg x)
                                        &&
                                        (for_all3b
                                           (fun x ->
                                              fun y ->
                                                fun matching ->
                                                  unif ~matching ((gid)
                                                    [@trace ]) depth env
                                                    c_depth x y) args_of_g xs
                                           [] false)
                                  | matching::ms ->
                                      (unif ~matching ((gid)[@trace ]) depth
                                         env c_depth arg x)
                                        &&
                                        (for_all3b
                                           (fun x ->
                                              fun y ->
                                                fun matching ->
                                                  unif ~matching ((gid)
                                                    [@trace ]) depth env
                                                    c_depth x y) args_of_g xs
                                           ms false)))
                    with
                    | false ->
                        (T.undo old_trail ();
                         raise
                           (Trace_ppx_runtime.Runtime.TREC_CALL
                              ((Obj.repr
                                  (backchain depth p (k, arg, args_of_g, gs)
                                     ((gid)[@trace ]) next alts lvl)),
                                (Obj.repr cs))))
                    | true ->
                        let oldalts = alts in
                        let alts =
                          if cs = []
                          then alts
                          else
                            {
                              program = p;
                              adepth = depth;
                              agoal_hd = k;
                              ogoal_arg = arg;
                              ogoal_args = args_of_g;
                              agid = ((gid)[@trace ]);
                              goals = gs;
                              stack = next;
                              trail = old_trail;
                              state = (!CS.state);
                              clauses = cs;
                              lvl;
                              next = alts
                            } in
                        (match c_hyps with
                         | [] ->
                             (match gs with
                              | [] ->
                                  raise
                                    (Trace_ppx_runtime.Runtime.TREC_CALL
                                       ((Obj.repr (pop_andl alts next)),
                                         (Obj.repr lvl)))
                              | { depth; program; goal;
                                  gid = ((gid)[@trace ]) }::gs ->
                                  raise
                                    (Trace_ppx_runtime.Runtime.TREC_CALL
                                       ((Obj.repr
                                           (run depth program goal ((gid)
                                              [@trace ]) gs next alts)),
                                         (Obj.repr lvl))))
                         | h::hs ->
                             let next =
                               if gs = []
                               then next
                               else FCons (lvl, gs, next) in
                             let h =
                               move ~adepth:depth ~from:c_depth ~to_:depth
                                 env h in
                             let hs =
                               List.map
                                 (fun x ->
                                    ((make_subgoal)[@inlined ]) ((gid)
                                      [@trace ]) ~depth p
                                      (move ~adepth:depth ~from:c_depth
                                         ~to_:depth env x)) hs in
                             let ((gid)[@trace ]) =
                               make_subgoal_id gid (((depth, h))[@trace ]) in
                             raise
                               (Trace_ppx_runtime.Runtime.TREC_CALL
                                  ((Obj.repr
                                      (run depth p h ((gid)[@trace ]) hs next
                                         alts)), (Obj.repr oldalts))))))) in
           let elapsed = (Unix.gettimeofday ()) -. wall_clock in
           Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "select" false
             None elapsed;
           rc
         with
         | Trace_ppx_runtime.Runtime.TREC_CALL (f, x) ->
             let elapsed = (Unix.gettimeofday ()) -. wall_clock in
             (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "select" true
                None elapsed;
              Obj.obj f (Obj.obj x))
         | e ->
             let elapsed = (Unix.gettimeofday ()) -. wall_clock in
             (Trace_ppx_runtime.Runtime.exit ~runtime_id:(!rid) "select"
                false (Some e) elapsed;
              raise e))
      and cut ((gid)[@trace ]) gs next alts lvl =
        let rec prune
          ({ agid = ((agid)[@trace ]); clauses; adepth = depth; agoal_hd = hd
             } as alts)
          =
          if alts == lvl
          then alts
          else
            (if true
             then
               Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                 ~goal_id:(Util.UUID.hash agid) "user:cut"
                 [Trace_ppx_runtime.Runtime.J
                    ((pplist (ppclause ~depth ~hd) " | "), clauses)];
             prune alts.next) in
        let alts = prune alts in
        if alts == noalts then ((T.cut_trail)[@inlined ]) ();
        (match gs with
         | [] -> pop_andl alts next lvl
         | { depth; program; goal; gid = ((gid)[@trace ]) }::gs ->
             run depth program goal ((gid)[@trace ]) gs next alts lvl)
      and pop_andl alts next lvl =
        match next with
        | FNil ->
            (match resume_all () with
             | None ->
                 (Fmt.fprintf Fmt.std_formatter
                    "Undo triggered by goal resumption\n%!";
                  raise
                    (Trace_ppx_runtime.Runtime.TREC_CALL
                       ((Obj.repr next_alt), (Obj.repr alts))))
             | Some ({ depth; program; goal; gid = ((gid)[@trace ]) }::gs) ->
                 run depth program goal ((gid)[@trace ]) gs FNil alts lvl
             | Some [] -> alts)
        | FCons (_, [], _) -> anomaly "empty stack frame"
        | FCons
            (lvl, { depth; program; goal; gid = ((gid)[@trace ]) }::gs, next)
            -> run depth program goal ((gid)[@trace ]) gs next alts lvl
      and resume_all () =
        (let ok = ref true in
         let to_be_resumed = ref [] in
         while (!ok) && ((!CS.to_resume) <> []) do
           (match !CS.to_resume with
            | ({ kind = Unification { adepth; bdepth; env; a; b; matching } }
                 as dg)::rest
                ->
                (CS.remove_old dg;
                 CS.to_resume := rest;
                 if true
                 then
                   Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                     "user:resume-unif"
                     [Trace_ppx_runtime.Runtime.J
                        (((fun fmt ->
                             fun () ->
                               Fmt.fprintf fmt
                                 "@[<hov 2>^%d:%a@ == ^%d:%a@]\n%!" adepth
                                 (uppterm adepth [] 0 empty_env) a bdepth
                                 (uppterm bdepth [] adepth env) b)), ())];
                 ok :=
                   (unif ~matching ((UUID.make ())[@trace ]) adepth env
                      bdepth a b))
            | ({ kind = Constraint dpg } as c)::rest ->
                (CS.remove_old c;
                 CS.to_resume := rest;
                 to_be_resumed := (dpg :: (!to_be_resumed)))
            | _ -> anomaly "Unknown constraint type")
           done;
         if !ok
         then
           (if (!CS.new_delayed) <> []
            then
              Some
                (Constraints.resumption
                   ((Constraints.propagation ()) @ (!to_be_resumed)))
            else Some (Constraints.resumption (!to_be_resumed)))
         else None : goal list option)
      and next_alt alts =
        if alts == noalts
        then raise No_clause
        else
          (let { program = p; clauses; agoal_hd = k; ogoal_arg = arg;
                 ogoal_args = args; agid = ((gid)[@trace ]); goals = gs;
                 stack = next; trail = old_trail; state = old_state;
                 adepth = depth; lvl; next = alts }
             = alts in
           T.undo ~old_trail ~old_state ();
           backchain depth p (k, arg, args, gs) ((gid)[@trace ]) next alts
             lvl clauses) in
      fun ?max_steps ->
        fun ?(delay_outside_fragment= false) ->
          fun
            { compiled_program; chr; initial_depth; initial_goal;
              initial_runtime_state; assignments; symbol_table; builtins }
            ->
            let { Fork.exec = exec; get; set } = Fork.fork () in
            set orig_prolog_program compiled_program;
            set Constraints.chrules chr;
            set T.initial_trail T.empty;
            set T.trail T.empty;
            set T.last_call false;
            set CS.new_delayed [];
            set CS.to_resume [];
            set CS.Ugly.delayed [];
            set steps_bound max_steps;
            set delay_hard_unif_problems delay_outside_fragment;
            set steps_made 0;
            set CS.state initial_runtime_state;
            set C.table symbol_table;
            set FFI.builtins builtins;
            set rid (!max_runtime_id);
            (let search =
               exec
                 (fun () ->
                    if true
                    then
                      Trace_ppx_runtime.Runtime.info ~runtime_id:(!rid)
                        "dev:trail:init"
                        [Trace_ppx_runtime.Runtime.J
                           (((fun fmt -> fun () -> T.print_trail fmt)), ())];
                    T.initial_trail := (!T.trail);
                    run initial_depth (!orig_prolog_program) initial_goal
                      ((UUID.make ())[@trace ]) [] FNil noalts noalts) in
             let destroy () =
               exec (fun () -> T.undo ~old_trail:T.empty ()) () in
             let next_solution = exec next_alt in
             incr max_runtime_id;
             { search; next_solution; destroy; exec; get })
    ;;do_make_runtime := make_runtime
  end 
open Mainloop
let mk_outcome search get_cs assignments =
  try
    let alts = search () in
    let (syn_csts, state, qargs, pp_ctx) = get_cs () in
    let solution =
      {
        assignments;
        constraints = syn_csts;
        state;
        output = (output qargs assignments state);
        pp_ctx
      } in
    ((Success solution), alts)
  with | No_clause -> (Failure, noalts)
  | No_more_steps -> (NoMoreSteps, noalts)
let execute_once ?max_steps  ?delay_outside_fragment  exec =
  auxsg := [];
  (let { search; get } = make_runtime ?max_steps ?delay_outside_fragment exec in
   fst
     (mk_outcome search
        (fun () ->
           ((get CS.Ugly.delayed), ((get CS.state) |> State.end_execution),
             (exec.query_arguments),
             { Data.uv_names = (ref (get Pp.uv_names)); table = (get C.table)
             })) exec.assignments))
let execute_loop ?delay_outside_fragment  exec ~more  ~pp  =
  let { search; next_solution; get } =
    make_runtime ?delay_outside_fragment exec in
  let k = ref noalts in
  let do_with_infos f =
    let time0 = Unix.gettimeofday () in
    let (o, alts) =
      mk_outcome f
        (fun () ->
           ((get CS.Ugly.delayed), ((get CS.state) |> State.end_execution),
             (exec.query_arguments),
             { Data.uv_names = (ref (get Pp.uv_names)); table = (get C.table)
             })) exec.assignments in
    let time1 = Unix.gettimeofday () in k := alts; pp (time1 -. time0) o in
  do_with_infos search;
  while (!k) != noalts do
    if not (more ())
    then k := noalts
    else
      (try do_with_infos (fun () -> next_solution (!k))
       with | No_clause -> (pp 0.0 Failure; k := noalts))
    done
let print_constraints () = CS.print Fmt.std_formatter (CS.contents ())
let pp_stuck_goal ?pp_ctx  fmt s = CS.pp_stuck_goal ?pp_ctx fmt s
let is_flex = HO.is_flex
let deref_uv = HO.deref_uv
let deref_appuv = HO.deref_appuv
let deref_head = HO.deref_head
let make_runtime = Mainloop.make_runtime
let lp_list_to_list = Clausify.lp_list_to_list
let list_to_lp_list = HO.list_to_lp_list
let split_conj = Clausify.split_conj
let mkAppArg = HO.mkAppArg
let subst ~depth  = HO.subst depth
let move = HO.move
let hmove = HO.hmove
let make_index = make_index
let clausify1 = Clausify.clausify1
let mkinterval = C.mkinterval
let mkAppL = C.mkAppL
let expand_uv ~depth  r ~lvl  ~ano  =
  let (t, assignment) = HO.expand_uv ~depth r ~lvl ~ano in
  option_iter (fun (r, _, assignment) -> r @:= assignment) assignment; t
let expand_appuv ~depth  r ~lvl  ~args  =
  let (t, assignment) = HO.expand_appuv ~depth r ~lvl ~args in
  option_iter (fun (r, _, assignment) -> r @:= assignment) assignment; t

