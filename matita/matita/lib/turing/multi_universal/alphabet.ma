(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic   
    ||A||  Library of Mathematics, developed at the Computer Science 
    ||T||  Department of the University of Bologna, Italy.           
    ||I||                                                            
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_____________________________________________________________*)

include "basics/finset.ma".
include "basics/lists/list.ma".

inductive unialpha : Type[0] ≝ 
| bit  : bool → unialpha
| null : unialpha
| bar  : unialpha.

definition unialpha_eq ≝ 
  λa1,a2.match a1 with
  [ bit x ⇒ match a2 with [ bit y ⇒ ¬ xorb x y | _ ⇒ false ]
  | bar ⇒ match a2 with [ bar ⇒ true | _ ⇒ false ] 
  | null ⇒ match a2 with [ null ⇒ true | _ ⇒ false ] ].
  
definition DeqUnialpha ≝ mk_DeqSet unialpha unialpha_eq ?.
* [ #x * [ #y cases x cases y normalize % // #Hfalse destruct
         | *: normalize % #Hfalse destruct ]
  | *: * [1,4: #y ] normalize % #H1 destruct % ]
qed.

lemma unialpha_unique : 
  uniqueb DeqUnialpha [bit true;bit false;null;bar] = true.
// qed.

lemma unialpha_complete :∀x:DeqUnialpha. 
  memb ? x [bit true;bit false;null;bar] = true.
* // * //
qed.

definition FSUnialpha ≝ 
  mk_FinSet DeqUnialpha [bit true;bit false;null;bar] 
  unialpha_unique unialpha_complete.

unification hint  0 ≔ ; 
    X ≟ FSUnialpha
(* ---------------------------------------- *) ⊢ 
    unialpha ≡ FinSetcarr X.
    
(*************************** testing characters *******************************)
definition is_bit ≝ λc.match c with [ bit _ ⇒ true | _ ⇒ false ].
definition is_bar ≝ λc:DeqUnialpha. c == bar.
definition is_null ≝ λc:DeqUnialpha. c == null.

definition only_bits ≝ λl.
  ∀c.mem ? c l → is_bit c = true.

definition no_bars ≝ λl.
  ∀c.mem ? c l → is_bar c = false.
