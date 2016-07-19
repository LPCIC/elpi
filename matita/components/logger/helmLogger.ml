(* $Id: helmLogger.ml 5769 2006-01-08 18:00:22Z sacerdot $ *)

open Printf

(* HTML simulator (first in its kind) *)

type html_tag =
 [ `T of string
 | `L of html_tag list 
 | `BR
 | `DIV of int * string option * html_tag
 ]

type html_msg = [ `Error of html_tag | `Msg of html_tag ]

type logger_fun = ?append_NL:bool -> html_msg -> unit

let rec string_of_html_tag =
  let rec aux indent =
    let indent_str = String.make indent ' ' in
    function
    | `T s -> s
    | `L msgs ->
        String.concat ("\n" ^ indent_str) (List.map (aux indent) msgs)
    | `BR -> "\n" ^ indent_str
    | `DIV (local_indent, _, tag) ->
        "\n" ^ indent_str ^ aux (indent + local_indent) tag
  in
  aux 0

let string_of_html_msg = function
  | `Error tag -> "Error: " ^ string_of_html_tag tag
  | `Msg tag -> string_of_html_tag tag

let rec html_of_html_tag = function
  | `T s -> s
  | `L msgs ->
      sprintf "<ul>\n%s\n</ul>"
        (String.concat "\n"
          (List.map
            (fun msg -> sprintf "<li>%s</li>" (html_of_html_tag msg))
            msgs))
  | `BR -> "<br />\n"
  | `DIV (indent, color, tag) ->
      sprintf "<div style=\"%smargin-left:%fcm\">\n%s\n</div>"
        (match color with None -> "" | Some color -> "color: " ^ color ^ "; ")
        (float_of_int indent *. 0.5)
        (html_of_html_tag tag)

let html_of_html_msg =
  function
    | `Error tag -> "<b>Error: " ^ html_of_html_tag tag ^ "</b>"
    | `Msg tag -> html_of_html_tag tag

let log_callbacks = ref []

let register_log_callback logger_fun =
  log_callbacks := !log_callbacks @ [ logger_fun ]

let log ?append_NL html_msg =
  List.iter (fun logger_fun -> logger_fun ?append_NL html_msg) !log_callbacks

