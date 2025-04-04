(* elpi: embedded lambda prolog interpreter                                  *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

open Elpi_util
open Elpi_lexer_config.Lexer_config

exception ParseError of Util.Loc.t * string

(* this is the input of the parser functor in grammar.mly, it ties the knot:
   accumulate requires to call the same parser on another file, but file/module
   resolution is not a parser business *)

module type ParseFile = sig
  val parse_file : ?cwd:string -> string -> Ast.Program.parser_output list
  val get_current_client_loc_payload : unit -> Obj.t option
  val set_current_clent_loc_pyload : Obj.t -> unit
end

let rec substrings i len_s s =
  if len_s - i >= 0 then
    String.sub s 0 i :: substrings (i+1) len_s s
  else []
let substrings s = List.rev @@ substrings 1 (String.length s) s

let find_sub tab s =
  let rec aux = function
    | [] -> raise Not_found
    | x :: xs ->
        try Hashtbl.find tab x
        with Not_found -> aux xs
  in
    aux (substrings s)

let precedence_of, umax_precedence, appl_precedence, inf_precedence =
  let tab = Hashtbl.create 21 in
  List.iteri (fun level { tokens; fixity } ->
    List.iter (function
      | Extensible { start; fixed; _ } ->
          Hashtbl.add tab start (fixity,level);
          List.iter (fun tok -> Hashtbl.add tab tok (fixity,level)) fixed
      | Fixed { the_token; _ } ->
          Hashtbl.add tab the_token (fixity,level)
      ) tokens;
    ) mixfix_symbols;
  let umax_precedence = List.length mixfix_symbols in
  let appl_precedence = umax_precedence + 1 in
  let inf_precedence = appl_precedence + 1 in (* greater than any used precedence*)
  (fun s ->
    try
      let fixity, prec = find_sub tab s in
      (*Format.eprintf "Printer: found %s %a %d\n%!" s pp_fixity (fst x) (snd x);*)
      Some fixity, prec
    with Not_found ->
      (*Format.eprintf "Printer: not found: %s\n%!" s;*)
      None, appl_precedence),
  umax_precedence, appl_precedence, inf_precedence

let comma_precedence = 1 + (snd @@ precedence_of ",")
let min_precedence = -1  (* minimal precedence in use *)
let lam_precedence = -1  (* precedence of lambda abstraction *)
let umin_precedence = 0   (* minimal user defined precedence *)

let pp_fixed fmt l =
  l |> List.iter (fun x -> Format.fprintf fmt "%s @ " x)

let pp_non_enclosed fmt = function
  | false -> ()
  | true -> Format.fprintf fmt " [*]"

let pp_tok_list fmt l =
  List.iter (function
    | Extensible { start; fixed; non_enclosed; _ } -> Format.fprintf fmt "%a%s..%a @ " pp_fixed fixed start pp_non_enclosed non_enclosed
    | Fixed { the_token; comment = None; _ } -> Format.fprintf fmt "%s @ " the_token
    | Fixed { the_token; comment = Some (id,_); _ } -> Format.fprintf fmt "%s (* see note %d *) @ " the_token id)
    l

let pp_tok_list_comments fmt l =
  List.iter (function
    | Extensible _ -> ()
    | Fixed { comment = None; _ } -> ()
    | Fixed { comment = Some (id,txt); _ } -> Format.fprintf fmt "%d: %s@ " id txt)
    l
    

let legacy_parser_compat_error =
  let open Format in
  let b = Buffer.create 80 in
  let fmt = formatter_of_buffer b in
  fprintf fmt "@[<v>";
  fprintf fmt "%s@;" "Mixfix directives are not supported by this parser.";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "The parser is based on token families.";
  fprintf fmt "%s@;" "A family is identified by some starting characters, for example";
  fprintf fmt "%s@;" "a token '+-->' belongs to the family of '+'. There is no need";
  fprintf fmt "%s@;" "to declare it.";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "All the tokens of a family are parsed with the same precedence and";
  fprintf fmt "%s@;" "associativity, for example 'x +--> y *--> z' is parsed as";
  fprintf fmt "%s@;" "'x +--> (y *--> z)' since the family of '*' has higher precedence";
  fprintf fmt "%s@;" "than the family of '+'.";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "Here the table of tokens and token families.";
  fprintf fmt "%s@;" "Token families are represented by the start symbols followed by '..'.";
  fprintf fmt "%s@;" "Tokens of families marked with [*] cannot end with the starting symbol,";
  fprintf fmt "%s@;" "eg `foo` is not an infix, while `foo is.";
  fprintf fmt "%s@;" "The listing is ordered by increasing precedence.";
  fprintf fmt "%s@;" "";
  pp_open_tbox fmt ();
  pp_set_tab fmt ();
  fprintf fmt "%-25s  " "fixity";
  pp_set_tab fmt ();
  fprintf fmt "| %s" "tokens / token families";
  pp_print_tab fmt ();
  let col1 = "--------------------------" in
  fprintf fmt "%s" col1;
  pp_print_tab fmt ();
  fprintf fmt "+ -----------------------------------";
  pp_print_tab fmt ();
  List.iter (fun { tokens; fixity; _ } ->
    fprintf fmt "%a" pp_fixity fixity; 
    pp_print_tab fmt ();
    let s =
      let b = Buffer.create 80 in
      let fmt = formatter_of_buffer b in
      pp_set_margin fmt 40;
      fprintf fmt "| ";
      pp_open_hovbox fmt 1;
      fprintf fmt "%a" pp_tok_list tokens;
      pp_close_box fmt ();
      pp_print_flush fmt ();
      let s = Buffer.contents b in
      let pad = "\n" ^ String.(make (length col1) ' ') in
      Re.Str.(global_replace (regexp_string "\n") pad s)
    in
    fprintf fmt "%s" s;
    pp_print_tab fmt ();
    ) mixfix_symbols;
  pp_close_tbox fmt ();
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "If the token is a valid mixfix, and you want the file to stay compatible";
  fprintf fmt "%s@;" "with Teyjus, you can ask Elpi to skip the directive. Eg:";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "% elpi:skip 2  // skips the next two lines";
  fprintf fmt "%s@;" "infixr ==> 120.";
  fprintf fmt "%s@;" "infixr || 120.";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "As a debugging facility one can ask Elpi to print the AST in order to";
  fprintf fmt "%s@;" "verify how the text was parsed. Eg:";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "echo 'MyFormula = a || b ==> c && d' | elpi -parse-term";
  fprintf fmt "%s@;" "";
  fprintf fmt "%s@;" "Notes:";
  List.iter (fun { tokens; _ } ->
    fprintf fmt "%a" pp_tok_list_comments tokens;
  ) mixfix_symbols;
  fprintf fmt "@]";
  pp_print_flush fmt ();
  Buffer.contents b
;;

let error_mixfix loc =
  raise (ParseError(loc,legacy_parser_compat_error))
