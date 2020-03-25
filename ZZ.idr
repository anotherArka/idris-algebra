module ZZ

import Useful_functions
import properties_of_Nat
import Quotient_type

%access public export
%access total

ZZ : Type
ZZ = (Nat, Nat)

ZZ_Rel : ZZ -> ZZ -> Type
ZZ_Rel (a, b) (c, d) = ((a + d) = (b + c))

ZZ_Rel_is_refl : {x : ZZ} -> (ZZ_Rel x x)
ZZ_Rel_is_refl {x = (a, b)} = plusCommutative a b

ZZ_Rel_is_sym : {x, y : ZZ} -> (ZZ_Rel x y) -> (ZZ_Rel y x)
ZZ_Rel_is_sym {x = (a, b)} {y = (c, d)} pf = let
  pf1 = plusCommutative a d
  pf2 = plusCommutative b c
  in
  trans (sym pf2) (trans (sym pf) pf1)

ZZ_Rel_is_trans : {x, y, z : ZZ} -> (ZZ_Rel x y) -> (ZZ_Rel y z) -> (ZZ_Rel x z)
ZZ_Rel_is_trans {x = (a, b)} {y = (c, d)} {z = (k, l)} pf1 pf2 = let
  pf3 = adding_equal_to_both_sides (a + d) (b + c) (c + l) (d + k) pf1 pf2
  pf4 = adding_four_2 a d c l
  pf5 = adding_four_2 b c d k
  pf6 = cong {f = (\x => (x + (k + b)))} (plusCommutative c d)
  pf7 = trans pf3 (trans pf5 (sym pf6))
  pf8 = trans (sym pf4) pf7
  pf9 = cancellation (c + d) (l + a) (k + b) pf8 
  in
  trans (plusCommutative a l) (trans pf9 (plusCommutative k b))

ZZ_canonical_from : ZZ -> ZZ
ZZ_canonical_from (Z, n) = (Z, n)
ZZ_canonical_from ((S m), Z) = ((S m), Z)
ZZ_canonical_from ((S m), (S n)) = ZZ_canonical_from (m, n)

ZZ_from_Integer : Integer -> ZZ
ZZ_from_Integer n = if_then_else (n >= 0) 
  (Nat_from_Integer n, 0)
  (0, Nat_from_Integer n) 

Eq_implies_ZZ_Rel : {x, y : ZZ} -> (x = y) -> (ZZ_Rel x y)
Eq_implies_ZZ_Rel {x = a} {y = a} Refl = ZZ_Rel_is_refl {x = a}  
  