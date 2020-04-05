module ZZ_plus

import properties_of_Nat
import ZZ

%access public export
%access total

ZZ_plus : ZZ -> ZZ -> ZZ
ZZ_plus (a, b) (c, d) = (a + c, b + d)

ZZ_plusCommutative : (a, b : ZZ) -> ((ZZ_plus a b) = (ZZ_plus b a))
ZZ_plusCommutative (a, b) (c, d) = 
  rewrite (plusCommutative a c) in (rewrite (plusCommutative b d) in Refl)

ZZ_plusAssociative : (a, b, c : ZZ) -> ((ZZ_plus a (ZZ_plus b c)) = (ZZ_plus (ZZ_plus a b) c))
ZZ_plusAssociative (a, b) (c, d) (m, n) = 
  rewrite (plusAssociative a c m) in 
    (rewrite (plusAssociative b d n) in Refl)

ZZ_plus_wrt_rel_helper : (a, b, c : ZZ) -> (ZZ_Rel a b) -> (ZZ_Rel (ZZ_plus a c) (ZZ_plus b c))
ZZ_plus_wrt_rel_helper (a, b) (c, d) (m, n) pf = let
  pf1 = adding_four_3 a m d n
  pf2 = adding_four_3 b n c m
  pf3 = adding_equal_to_both_sides (a + d) (b + c) (m + n) (n + m) pf (plusCommutative m n)
  in
  trans pf1 (trans pf3 (sym pf2))

||| Proof that ZZ_plus respects ZZ_Rel  
ZZ_plus_wrt_rel : (a, b, c, d : ZZ) -> (ZZ_Rel a b) -> (ZZ_Rel c d) -> (ZZ_Rel (ZZ_plus a c) (ZZ_plus b d))
ZZ_plus_wrt_rel a b c d pf1 pf2 = let
  pf3 = ZZ_plus_wrt_rel_helper a b c pf1
  pf4 = ZZ_plus_wrt_rel_helper c d b pf2
  pf5 = Eq_implies_ZZ_Rel (ZZ_plusCommutative b c)
  pf6 = Eq_implies_ZZ_Rel (ZZ_plusCommutative b d)
  in
   ZZ_Rel_is_trans pf3
  (ZZ_Rel_is_trans pf5
  (ZZ_Rel_is_trans pf4
  (ZZ_Rel_is_sym pf6)))

||| Proof that a + ZZ.zero = a
ZZ_zero_is_additive_identity : (a : ZZ) -> (ZZ_plus ZZ.zero a = a)
ZZ_zero_is_additive_identity (a, b) = Refl


