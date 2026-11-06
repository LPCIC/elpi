(* prints the stub of the plugin, its documentation: elpi-json.plugin.elpi *)
let () = Elpi.API.BuiltIn.document_fmt Format.std_formatter Elpi_json.builtins
