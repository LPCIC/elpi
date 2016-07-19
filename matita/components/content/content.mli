(* Copyright (C) 2000, HELM Team.
 * 
 * This file is part of HELM, an Hypertextual, Electronic
 * Library of Mathematics, developed at the Computer Science
 * Department, University of Bologna, Italy.
 * 
 * HELM is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 * 
 * HELM is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with HELM; if not, write to the Free Software
 * Foundation, Inc., 59 Temple Place - Suite 330, Boston,
 * MA  02111-1307, USA.
 * 
 * For details, see the HELM World-Wide-Web page,
 * http://cs.unibo.it/helm/.
 *)

type id = string;;
type joint_recursion_kind =
 [ `Recursive of int list (* decreasing arguments *)
 | `CoRecursive
 | `Inductive of int    (* paramsno *)
 | `CoInductive of int  (* paramsno *)
 ]
;;

type var_or_const = Var | Const;;

type 'term declaration =
       { dec_name : string option;
         dec_id : id ;
         dec_inductive : bool;
         dec_aref : string;
         dec_type : 'term 
       }
;;

type 'term definition =
       { def_name : string option;
         def_id : id ;
         def_aref : string ;
         def_term : 'term ;
         def_type : 'term 
       }
;;

type 'term inductive =
       { inductive_id : id ;
         inductive_name : string;
         inductive_kind : bool;
         inductive_type : 'term;
         inductive_constructors : 'term declaration list
       }
;;

type 'term decl_context_element = 
       [ `Declaration of 'term declaration
       | `Hypothesis of 'term declaration
       ]
;;

type ('term,'proof) def_context_element = 
       [ `Proof of 'proof
       | `Definition of 'term definition
       ]
;;

type ('term,'proof) in_joint_context_element =
       [ `Inductive of 'term inductive
       | 'term decl_context_element
       | ('term,'proof) def_context_element
       ]
;;

type ('term,'proof) joint =
       { joint_id : id ;
         joint_kind : joint_recursion_kind ;
         joint_defs : ('term,'proof) in_joint_context_element list
       }
;;

type ('term,'proof) joint_context_element = 
       [ `Joint of ('term,'proof) joint ]
;;

type 'term proof = 
      { proof_name : string option;
        proof_id   : id ;
        proof_context : 'term in_proof_context_element list ;
        proof_apply_context: 'term proof list;
        proof_conclude : 'term conclude_item
      }

and 'term in_proof_context_element =
       [ 'term decl_context_element
       | ('term,'term proof) def_context_element 
       | ('term,'term proof) joint_context_element
       ]

and 'term conclude_item =
       { conclude_id : id; 
         conclude_aref : string;
         conclude_method : string;
         conclude_args : ('term arg) list ;
         conclude_conclusion : 'term option 
       }

and 'term arg =
         Aux of string
       | Premise of premise
       | Lemma of lemma
       | Term of bool * 'term (* inferrable, term *)
       | ArgProof of 'term proof
       | ArgMethod of string (* ???? *)

and premise =
       { premise_id: id;
         premise_xref : string ;
         premise_binder : string option;
         premise_n : int option;
       }

and lemma =
       { lemma_id: id;
         lemma_name : string;
         lemma_uri: string
       }
;;
 
type 'term conjecture = id * int * 'term context * 'term

and 'term context = 'term hypothesis list

and 'term hypothesis =
 ['term decl_context_element | ('term,'term proof) def_context_element ] option
;;

type 'term in_object_context_element =
       [ `Decl of var_or_const * 'term decl_context_element
       | `Def of var_or_const * 'term * ('term,'term proof) def_context_element
       | ('term,'term proof) joint_context_element
       ]
;;

type 'term cobj  = 
        id *                            (* id *)
        'term conjecture list option *  (* optional metasenv *) 
        'term in_object_context_element (* actual object *)
;;
