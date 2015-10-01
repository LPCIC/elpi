module sockets.

local read_token_rec in_stream -> string -> string -> o.

read_token InStream Result:- 
%        print "read_token\n",
        flush std_out,
        read_token_rec InStream "" Result.

read_token_rec InStream Acc Result:-
        input InStream 1 Byte,
	B is string_to_int Byte,
        ((B = 128, 
%        print "found EOF\n",
        Result = Acc);
        (NewAcc is Acc ^ Byte,
        read_token_rec InStream NewAcc Result)).

close_connection:-
        print "closing MathWeb connection\n",
        flush std_out,
        lclam_sockets (lclam_server_socket ServIn ServOut) (lclam_client_socket ClientIn ClientOut),
        print "closing MathWeb connection\n",
        flush std_out,
        close_in ServIn,
        close_in ClientIn,
        print "hello\n",
        close_out ServOut,
        close_out ClientOut.


end
