sig sockets.

kind lclam_socket type.

type lclam_server_socket in_stream -> out_stream -> lclam_socket.
type lclam_client_socket in_stream -> out_stream -> lclam_socket.

type lclam_sockets lclam_socket -> lclam_socket -> o.

type read_result in_stream -> string -> o.
type read_token in_stream -> string -> o.

type close_connection o.

end
