module Rational

import ZZ
import ZZ_mult  
import ZZ_implementations

%access public export
%access total

Rational : Type 
Rational = (ZZ, Nat)

zero : Rational
zero = (0, Z)

Rational_Rel : Rational -> Rational -> Type
Rational_Rel (p1, q1) (p2, q2) = ZZ_Rel (p1 * (S q2, 0)) (p2 * (S q1, 0)) 

Rational_Rel_is_refl : {rat : Rational} -> (Rational_Rel rat rat)
Rational_Rel_is_refl {rat = (p, q)} = ZZ_Rel_is_refl

Rational_Rel_is_sym : {mouse, rat : Rational} -> (Rational_Rel mouse rat) -> (Rational_Rel rat mouse)
Rational_Rel_is_sym {mouse = (a, b)} {rat = (c, d)} pfRel = ZZ_Rel_is_sym pfRel

Rational_Rel_is_trans : {mouse, rat, hamster : Rational} -> 
  (Rational_Rel mouse rat) -> (Rational_Rel rat hamster) -> (Rational_Rel mouse hamster)
Rational_Rel_is_trans {mouse = (a, b)} {rat = (p,q)} {hamster = (x, y)} pf1 pf2 = let
  pf3 = ZZ_mult_wrt_rel (a * (S q, 0)) (p * (S b, 0)) 
    (p * (S y, 0)) (x * (S q, 0)) pf1 pf2
  in
  ?rhs_rational_is_trans