/*

File: pretty_print.sig
Author: Alan Smaill / James Brotherston
Description:  Pretty printing primitives; based on Paulson's ML example
Last Modified: 14th August 2002.

*/

% could be adapted to return list of strings;
% this version outputs to given stream.

sig pretty_print.

kind  thing   type.  % type of marked up syntax

type  blo     int -> list thing -> thing.
                     % a block, with an indent level,
                     % used if a break precedes the block,
                     % and a list of things forming the block --
                     % may have nested block structure.
type  str     string -> thing.
                     % string (will not get broken)
type  abstr   int -> (A -> list thing)  -> thing.
                     % special treatment for abstractions 
type  brk     int -> thing.
                     % possible break point; argument is space included
                     % if there is no break.
type  pr      out_stream -> thing -> int -> o.
                     % to output formatted text, for given line width
type  lvar    (A -> thing).  % type coercion
                             % -- use only around abstracted vars.


end
