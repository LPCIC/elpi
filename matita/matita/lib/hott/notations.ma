notation "1" with precedence 90 for @{'idpath}.

notation < "hvbox(l1 break # _(term 90 F) (term 47 l2))"
  non associative with precedence 47
  for @{'transport $F $l1 $l2 }.

notation > "hvbox(l1 break # l2)"
  right associative with precedence 47
  for @{'transport ? $l1 $l2 }.

notation "hvbox(l1 break @ l2)"
  right associative with precedence 49
  for @{'append $l1 $l2 }.

(* exists *******************************************************************)

notation "hvbox(∃ _ break . p)"
 with precedence 20
for @{'exists $p }.

notation < "hvbox(\exists ident i : ty break . p)"
 right associative with precedence 20
for @{'exists (\lambda ${ident i} : $ty. $p) }.

notation < "hvbox(\exists ident i break . p)"
  with precedence 20
for @{'exists (\lambda ${ident i}. $p) }.

notation "hvbox(〈term 19 a, break term 19 b〉)" 
with precedence 90 for @{ 'mk_exists $a $b }.

(*
notation < "hvbox(\exists ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'exists ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.
*)

notation > "\exists list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'exists (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'exists (λ${ident x}.$acc)} } }
       }.

(*
notation > "hvbox(∃∃ ident x0 break . term 19 P0 break & term 19 P1)"
 non associative with precedence 20
 for @{ 'exists2 (λ${ident x0}.$P0) (λ${ident x0}.$P1) }.

notation < "hvbox(∃∃ ident x0 break . term 19 P0 break & term 19 P1)"
 non associative with precedence 20
 for @{ 'exists2 (λ${ident x0}:$T0.$P0) (λ${ident x0}:$T0.$P1) }.

(* sigma ********************************************************************)

notation < "hvbox(\Sigma ident i : ty break . p)"
 left associative with precedence 20
for @{'sigma (\lambda ${ident i} : $ty. $p) }.

notation < "hvbox(\Sigma ident i break . p)"
 with precedence 20
for @{'sigma (\lambda ${ident i}. $p) }.

(*
notation < "hvbox(\Sigma ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'sigma ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.
*)

notation > "\Sigma list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'sigma (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'sigma (λ${ident x}.$acc)} } }
       }.

notation "hvbox(« term 19 a, break term 19 b»)" 
with precedence 90 for @{ 'dp $a $b }.

(* dependent pairs (i.e. Sigma with predicate in Type[0])  ********************)

notation < "hvbox(𝚺 ident i : ty break . p)"
 left associative with precedence 20
for @{'dpair (\lambda ${ident i} : $ty. $p) }.

notation < "hvbox(𝚺 ident i break . p)"
 with precedence 20
for @{'dpair (\lambda ${ident i}. $p) }.

(*
notation < "hvbox(𝚺 ident i opt (: ty) break . p)"
  right associative with precedence 20
for @{ 'dpair ${default
  @{\lambda ${ident i} : $ty. $p}
  @{\lambda ${ident i} . $p}}}.
*)

notation > "𝚺 list1 ident x sep , opt (: T). term 19 Px"
  with precedence 20
  for ${ default
          @{ ${ fold right @{$Px} rec acc @{'dpair (λ${ident x}:$T.$acc)} } }
          @{ ${ fold right @{$Px} rec acc @{'dpair (λ${ident x}.$acc)} } }
       }.

notation "hvbox(❬ term 19 a, break term 19 b❭)" 
with precedence 90 for @{ 'mk_DPair $a $b }.
*)

(* equality, conguence ******************************************************)

notation > "hvbox(a break = b)" 
  non associative with precedence 45
for @{ 'eq ? $a $b }.

notation < "hvbox(term 46 a break maction (=) (=\sub t) term 46 b)" 
  non associative with precedence 45
for @{ 'eq $t $a $b }.

notation > "hvbox(n break ≅ m)"
  non associative with precedence 45
for @{ 'congruent $n $m ? }.

notation < "hvbox(term 46 n break ≅ _ term 90 p term 46 m)"
  non associative with precedence 45
for @{ 'congruent $n $m $p }.

notation "hvbox(n break ≡ m)"
  non associative with precedence 45
for @{ 'equiv $n $m }.

(*
(* other notations **********************************************************)

notation "hvbox(\langle term 19 a, break term 19 b\rangle)" 
with precedence 90 for @{ 'pair $a $b}.

notation "hvbox(x break \times y)" with precedence 70
for @{ 'product $x $y}.

notation < "\fst \nbsp term 90 x" with precedence 69 for @{'pi1a $x}.
notation < "\snd \nbsp term 90 x" with precedence 69 for @{'pi2a $x}.

notation < "\fst \nbsp term 90 x \nbsp term 90 y" with precedence 69 for @{'pi1b $x $y}.
notation < "\snd \nbsp term 90 x \nbsp term 90 y" with precedence 69 for @{'pi2b $x $y}.

notation > "\fst" with precedence 90 for @{'pi1}.
notation > "\snd" with precedence 90 for @{'pi2}.
*)

notation "hvbox(a break \to b)" 
  right associative with precedence 20
for @{ \forall $_:$a.$b }.

notation < "hvbox(a break \to b)" 
  right associative with precedence 20
for @{ \Pi $_:$a.$b }.

(*
notation "hvbox(a break \leq b)" 
  non associative with precedence 45
for @{ 'leq $a $b }.

notation "hvbox(a break \geq b)" 
  non associative with precedence 45
for @{ 'geq $a $b }.

notation "hvbox(a break \lt b)" 
  non associative with precedence 45
for @{ 'lt $a $b }.

notation "hvbox(a break \gt b)" 
  non associative with precedence 45
for @{ 'gt $a $b }.

notation > "hvbox(a break \neq b)" 
  non associative with precedence 45
for @{ 'neq ? $a $b }.

notation < "hvbox(a break maction (\neq) (\neq\sub t) b)" 
  non associative with precedence 45
for @{ 'neq $t $a $b }.

notation "hvbox(a break \nleq b)" 
  non associative with precedence 45
for @{ 'nleq $a $b }.

notation "hvbox(a break \ngeq b)" 
  non associative with precedence 45
for @{ 'ngeq $a $b }.

notation "hvbox(a break \nless b)" 
  non associative with precedence 45
for @{ 'nless $a $b }.

notation "hvbox(a break \ngtr b)" 
  non associative with precedence 45
for @{ 'ngtr $a $b }.

notation "hvbox(a break \divides b)"
  non associative with precedence 45
for @{ 'divides $a $b }.

notation "hvbox(a break \ndivides b)"
  non associative with precedence 45
for @{ 'ndivides $a $b }.

notation "hvbox(a break + b)" 
  left associative with precedence 55
for @{ 'plus $a $b }.

notation "hvbox(a break - b)" 
  left associative with precedence 55
for @{ 'minus $a $b }.

notation "hvbox(a break * b)" 
  left associative with precedence 60
for @{ 'times $a $b }.

notation "hvbox(a break \middot b)" 
  left associative with precedence 60
  for @{ 'middot $a $b }.

notation "hvbox(a break \mod b)" 
  left associative with precedence 60
for @{ 'module $a $b }.

notation < "a \frac b" 
  non associative with precedence 90
for @{ 'divide $a $b }.

notation "a \over b" 
  left associative with precedence 60
for @{ 'divide $a $b }.

notation "hvbox(a break / b)" 
  left associative with precedence 60
for @{ 'divide $a $b }.

notation "- term 65 a" with precedence 65 
for @{ 'uminus $a }.

notation "a !"
  non associative with precedence 80
for @{ 'fact $a }.

notation "\sqrt a" 
  non associative with precedence 65
for @{ 'sqrt $a }.

notation "hvbox(a break \lor b)" 
  left associative with precedence 30
for @{ 'or $a $b }.

notation "hvbox(a break \land b)" 
  left associative with precedence 35
for @{ 'and $a $b }.

notation "hvbox(\lnot a)" 
  non associative with precedence 40
for @{ 'not $a }.

notation > "hvbox(a break \liff b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.

notation "hvbox(a break \leftrightarrow b)" 
  left associative with precedence 25
for @{ 'iff $a $b }.


notation "hvbox(\Omega \sup term 90 A)" non associative with precedence 90
for @{ 'powerset $A }.
notation > "hvbox(\Omega ^ term 90 A)" non associative with precedence 90
for @{ 'powerset $A }.

notation < "hvbox({ ident i | term 19 p })" with precedence 90
for @{ 'subset (\lambda ${ident i} : $nonexistent . $p)}.

notation > "hvbox({ ident i | term 19 p })" with precedence 90
for @{ 'subset (\lambda ${ident i}. $p)}.

notation < "hvbox({ ident i ∈ term 19 s | term 19 p })" with precedence 90
for @{ 'comprehension $s (\lambda ${ident i} : $nonexistent . $p)}.

notation > "hvbox({ ident i ∈ term 19 s | term 19 p })" with precedence 90
for @{ 'comprehension $s (\lambda ${ident i}. $p)}.

notation "hvbox(a break ∈ b)" non associative with precedence 45
for @{ 'mem $a $b }.

notation "hvbox(a break ∉ b)" non associative with precedence 45
for @{ 'notmem $a $b }.

notation "hvbox(a break ≬ b)" non associative with precedence 45
for @{ 'overlaps $a $b }. (* \between *)

notation "hvbox(a break ⊆ b)" non associative with precedence 45
for @{ 'subseteq $a $b }. (* \subseteq *)

notation "hvbox(a break ∩ b)" left associative with precedence 60
for @{ 'intersects $a $b }. (* \cap *)

notation "hvbox(a break ∪ b)" left associative with precedence 55
for @{ 'union $a $b }. (* \cup *)

notation "hvbox({ term 19 a })" with precedence 90 for @{ 'singl $a}.

notation "hvbox(a break \approx b)" non associative with precedence 45 
  for @{ 'napart $a $b}.
        
notation "hvbox(a break # b)" non associative with precedence 45 
  for @{ 'apart $a $b}.
*)
    
notation "hvbox(a break \circ b)" 
  left associative with precedence 60
for @{ 'compose $a $b }.

(*
notation < "↓ \ensp a" with precedence 60 for @{ 'downarrow $a }.
notation > "↓ a" with precedence 60 for @{ 'downarrow $a }.

notation "hvbox(U break ↓ V)" non associative with precedence 60 for @{ 'fintersects $U $V }.

notation "↑a" with precedence 60 for @{ 'uparrow $a }.

notation "hvbox(a break ↑ b)" with precedence 60 for @{ 'funion $a $b }.

notation < "term 76 a \sup term 90 b" non associative with precedence 75 for @{ 'exp $a $b}.
notation > "a \sup term 90 b" non associative with precedence 75 for @{ 'exp $a $b}.
notation > "a ^ term 90 b"  non associative with precedence 75 for @{ 'exp $a $b}.
*)
notation "s ^ (-1)" non associative with precedence 75 for @{ 'invert $s }.
(*
notation < "s \sup (-1) x" non associative with precedence 90 for @{ 'invert_appl $s $x}. 

notation "| term 19 C |" with precedence 70 for @{ 'card $C }.

notation "\naturals" non associative with precedence 90 for @{'N}.
notation "\rationals" non associative with precedence 90 for @{'Q}.
notation "\reals" non associative with precedence 90 for @{'R}.
notation "\integers" non associative with precedence 90 for @{'Z}.
notation "\complexes" non associative with precedence 90 for @{'C}.

notation "\ee" with precedence 90 for @{ 'neutral }. (* ⅇ *)

notation > "x ⊩ y" with precedence 45 for @{'Vdash2 $x $y ?}.
notation > "x ⊩⎽ term 90 c y" with precedence 45 for @{'Vdash2 $x $y $c}.
notation "x (⊩ \sub term 90 c) y" with precedence 45 for @{'Vdash2 $x $y $c}.
notation > "⊩ " with precedence 65 for @{'Vdash ?}.
notation "(⊩ \sub term 90 c) " with precedence 65 for @{'Vdash $c}.

notation < "maction (mstyle color #ff0000 (­…­)) (t)" 
non associative with precedence 90 for @{'hide $t}.
*)
