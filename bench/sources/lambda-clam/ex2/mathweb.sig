

sig mathweb.

accum_sig lclam.

type mathweb_connect string -> int -> int -> X -> o.
type mathweb_get_service string -> string -> o.
type mathweb_apply string -> string -> (list (list string)) -> int -> (list (list string)) -> o.

type mathweb_leave_service string -> o.

type mathweb_args_to_string (list (list string)) -> string -> o.

type mathweb_read_result in_stream -> (list (list string)) -> o.
type mathweb_read_token in_stream -> string -> o.
type mathweb_read_token_rec in_stream -> string -> string -> o.

type mathweb_handle_byte string -> string -> o.
type mathweb_handle_token in_stream -> string -> (list (list string)) -> o.
type mathweb_handle_record in_stream -> (list (list string)) -> (list (list string)) -> o.

end

