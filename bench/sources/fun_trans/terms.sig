sig terms.

% ABSTRACT SYNTAX OF A SIMPLE FUNCTIONAL LANGUAGE

kind tm type.  % kind of terms


% TERMS OF THE LANGUAGE

type u tm.  % unit value

type pair tm -> tm -> tm.  % pair constructor
type fst tm -> tm.         % pair accessor (first)
type snd tm -> tm.         % pair accessor (second)

type inl tm -> tm.  % sum type constructor (left)
type inr tm -> tm.  % sum type constructor (right)

type case tm -> (tm -> tm) -> (tm -> tm) -> tm.  % sum type case switch

type lam (tm -> tm) -> tm.        % lambda abstraction
type rec (tm -> tm -> tm) -> tm.  % fixed point operator (recursion)
type app tm -> tm -> tm.          % function application

type abs_rtp tm -> tm.  % abstraction operator for recursive types
type rep_rtp tm -> tm.  % representation operator for recursive types


% BASIC OPERATIONS ON TERMS AND FUNCTIONS ON TERMS

% [tm_fun_linear +F] tests whether function [F] is linear in its argument,
% i.e. the number of occurrences of its parameter in the function body
% is 0 or 1, considering different case arms separately.
type tm_fun_linear (tm -> tm) -> o.

% [output_tm +Out +T] prints term [T] to output stream [Out].
type output_tm out_stream -> tm -> o.

% [print_tm +T] prints term [T] to standard output.
type print_tm tm -> o.


% INTERNAL OPERATIONS - USE WITH CAUTION
type tm_linear_aux tm -> o -> o -> o.
type tm_fun_linear_aux (tm -> tm) -> o -> o -> o.
