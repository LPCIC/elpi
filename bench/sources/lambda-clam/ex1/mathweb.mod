/* 

File: mathweb.mod
Author: Juergen Zimmer, jzimmer@mathweb.org
Description: Predicates for using MathWeb services
Last Modified: 25th Jan 2002

*/

module mathweb.

%-------------------------------------------------
%  initialise the connection to MathWeb, then call the lclam main loop in socket_read_write or command_pretty mode.
%-------------------------------------------------
mathweb_connect Hostname Serverport Clientport Mode :-
        output std_out "This is LClam in socket_read_write mode!\n",
        output std_out Hostname,
        output std_out "\n",
        flush std_out,
        
        open_socket Hostname Serverport ServIn ServOut,
        open_socket Hostname Clientport ClientIn ClientOut,
        ((interactive Mode => (lclam_sockets (lclam_server_socket ServIn ServOut) (lclam_client_socket ClientIn ClientOut) => lclam))).


%-------------------------------------------------
% read the service result from the input stream 
%-------------------------------------------------
mathweb_read_result InStream Result :-
        read_token InStream Token,
        mathweb_handle_token InStream Token Result,
        output std_out "incoming: ",
        printterm std_out Result,
        pprint_string "\n".

mathweb_handle_token InStream "formula" Result:-
        print "reading formula\n",
        read_token InStream String,
        Result = ((String::nil)::nil).

mathweb_handle_token InStream "record" Result:-
        mathweb_handle_record InStream nil Result.

mathweb_handle_token InStream "string" Result:-
        print "reading string\n",
        read_token InStream String,
        Result = ((String::nil)::nil).

mathweb_handle_token InStream "error" Result:-
        print "reading error\n",
        read_token InStream String,
        Result = (("error"::nil)::nil).

mathweb_handle_token InStream String Result:-
        print "unknown token: ",
        print String,
        print "\n",
        flush std_out,
        Result = (("error"::nil)::nil).


mathweb_handle_record InStream Rec Result:-
        print "reading record\n",
        read_token InStream Key,
        ((Key = "end-of-record",
        print "end of record found\n",
        flush std_out,
        Result = Rec);
        (read_token InStream Value,
        mathweb_handle_record InStream ((Key::Value::nil)::Rec) Result)).

%-------------------------------------------------
% request a service object from the MathWeb broker
%-------------------------------------------------
mathweb_get_service ServiceName Result:-
        lclam_sockets _ (lclam_client_socket In Out),
        output std_out "before enter(ServiceName)\n",
        flush std_out,
        Message is "enter('" ^ ServiceName ^ "')\x80",
        output Out Message,
        flush Out,
        output std_out "before read_result\n",
        mathweb_read_result In CallResult,
        ((Result::_)::_) = CallResult.


%-------------------------------------------------
% send a message to a service object 
% ToDo: must be improved in the future to take parameters 
%       as a list of Teyjus terms.
%-------------------------------------------------
mathweb_apply Service MethodName Arguments Timeout Result:-
        lclam_sockets _ (lclam_client_socket In Out),
        print "applyMethod()\n",
        flush std_out,
        mathweb_args_to_string Arguments ArgsString,
        Method is MethodName ^ "(" ^ ArgsString ^ ")",
        TimeString is (int_to_string Timeout),
        Message is "applyMethod('" ^ Service ^ "' " ^ Method ^ " timeout: " ^ TimeString ^ ")\x80",
        pprint_string "message:", 
        pprint_string Message, 
        flush std_out,
        output Out Message,
        flush Out,
        output std_out "before read_result\n",
        flush std_out,
        mathweb_read_result In Result.

%-------------------------------------------------
% leave a MathWeb service, i.e. kill the service object
%-------------------------------------------------
mathweb_leave_service Service:-
        lclam_sockets _ (lclam_client_socket In Out),
        output std_out "before leave(Service)\n",
        flush std_out,
        Message is "leave('" ^ Service ^ "')\x80",
        output Out Message,
        flush Out,
        %%        output std_out "before read_result\n",
        mathweb_read_result In _. 

mathweb_args_to_string nil "".

mathweb_args_to_string ((Feature::Value::nil)::Args) String:-
        mathweb_args_to_string Args RestString,
        String is Feature ^ ": " ^ Value ^ " " ^ RestString.




