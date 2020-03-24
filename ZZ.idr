module ZZ

import properties_of_Nat

%access public export

 ZZ : Type
 ZZ = (Nat, Nat)

 ZZ_Rel : ZZ -> ZZ -> Type
 ZZ_Rel (a, b) (c, d) = ((a + d) = (b + c))

 ZZ_Rel_is_refl : (a : ZZ) -> (ZZ_Rel a a)
 ZZ_Rel_is_refl (a, b) = plusCommutative a b

 ZZ_Rel_is_sym : (a : ZZ) -> (b : ZZ) -> (ZZ_Rel a b) -> (ZZ_Rel b a)
 ZZ_Rel_is_sym (a, b) (c, d) pf = let
  pf1 = plusCommutative a d
  pf2 = plusCommutative b c
  in
  trans (sym pf2) (trans (sym pf) pf1)

ZZ_Rel_is_trans : (a : ZZ) -> (b : ZZ) -> (c : ZZ) -> (ZZ_Rel a b) -> (ZZ_Rel b c) -> (ZZ_Rel a c)
ZZ_Rel_is_trans (a, b) (c, d) (k, l) pf1 pf2 = let
  pf3 = adding_equal_to_both_sides (a + d) (b + c) (c + l) (d + k) pf1 pf2
  pf4 = adding_four_2 a d c l
  pf5 = adding_four_2 b c d k
  pf6 = cong {f = (\x => (x + (k + b)))} (plusCommutative c d)
  pf7 = trans pf3 (trans pf5 (sym pf6))
  pf8 = trans (sym pf4) pf7
  pf9 = cancellation (c + d) (l + a) (k + b) pf8 
  in
  trans (plusCommutative a l) (trans pf9 (plusCommutative k b))
  