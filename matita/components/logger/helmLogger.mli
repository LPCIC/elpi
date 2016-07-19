
type html_tag =
  [ `BR
  | `L of html_tag list
  | `T of string
  | `DIV of int * string option * html_tag  (* indentation, color, tag *)
  ]
type html_msg = [ `Error of html_tag | `Msg of html_tag ]

  (** html_msg to plain text converter *)
val string_of_html_msg: html_msg -> string

  (** html_tag to plain text converter *)
val string_of_html_tag: html_tag -> string

  (** html_msg to html text converter *)
val html_of_html_msg: html_msg -> string

  (** html_tag to html text converter *)
val html_of_html_tag: html_tag -> string

type logger_fun = ?append_NL:bool -> html_msg -> unit

val register_log_callback: logger_fun -> unit

val log: logger_fun

