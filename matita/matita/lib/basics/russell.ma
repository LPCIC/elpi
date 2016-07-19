(*
    ||M||  This file is part of HELM, an Hypertextual, Electronic        
    ||A||  Library of Mathematics, developed at the Computer Science     
    ||T||  Department of the University of Bologna, Italy.                     
    ||I||                                                                 
    ||T||  
    ||A||  
    \   /  This file is distributed under the terms of the       
     \ /   GNU General Public License Version 2   
      V_______________________________________________________________ *)

include "basics/jmeq.ma".
include "basics/types.ma".

coercion inject nocomposites: ∀A.∀P:A → Prop.∀a.∀p:P a.Sig A P ≝ mk_Sig on a:? to Sig ??.
coercion eject nocomposites: ∀A.∀P:A → Prop.∀c:Sig A P.A ≝ pi1 on _c:Sig ?? to ?.
