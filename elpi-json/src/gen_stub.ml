(* prints the stub of the plugin, its documentation: json.builtins.elpi *)
let () = Elpi.API.BuiltIn.document_fmt Format.std_formatter Elpi_json.builtins
