/*
 *  Encoding of types. Polymorphism is not explicitly represented in
 *  types in this encoding; some aspects of polymorphism can be 
 *  captured through logic variables in the meta-logic. This encoding 
 *  is in a sense a shallow encoding.
 */

sig monotypes.

kind   ty    type.              % constructor for mono types

type   -->   ty -> ty -> ty.    % arrow type constructor
infixr -->   5.

type lst     ty -> ty.          % list type constructor
type num     ty.                % integer type
type bool    ty.                % boolean type
