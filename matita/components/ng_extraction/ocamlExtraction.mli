open OcamlExtractionTable

(* These commands have an effect iff OCAML_EXTRACTION is set *)

val print_open: #status as 'status -> NUri.uri list -> 'status
val print_ocaml_of_obj: #status as 'status -> NCic.obj -> 'status
val open_file: #status as 'status -> baseuri:string -> string -> 'status
val close_file: #status as 'status -> 'status
