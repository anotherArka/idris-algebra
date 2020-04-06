module Rational_ord

import ZZ
import ZZ_plus
import ZZ_mult
import ZZ_ord
import ZZ_implementations
import Rational
import Rational_minus

%access public export
%access total

Rational_greater_than_zero : Rational -> Bool
Rational_greater_than_zero (a, b) = ZZ_greater_than_zero a

Rational_strict_order : Rational -> Rational -> Bool
Rational_strict_order a b = Rational_greater_than_zero (Rational_minus a b)

LTEZero : Rational -> Type
LTEZero (a, b) = LTEZero a

LTE : Rational -> Rational -> Type
LTE a b = LTEZero (Rational_minus a b)

-- LTZero_respects_Rel_helper_1 : (a, b, r : Nat) -> 
--   ((plus (mult a (S r)) (mult b 0)) = (mult a (S r)))

-- LTZero_respects_Rel_helper_1 a b r = let
--   pf1 = multCommutative b 0
--   pf2 = cong {f = (\x => ((a * (S r)) + x))} pf1
--   pf3 = plusCommutative (a * (S r)) 0
--   in
--   trans pf2 pf3

-- LTZero_respects_Rel_helper_2 : (a, b, r, p, q, c : Nat) -> 
--   (plus (plus (mult a (S r)) (mult b 0)) (plus (mult p 0) (mult q (S c)))) = 
--   (plus (mult a (S r)) (mult q (S c)))

-- LTZero_respects_Rel_helper_2 a b r p q c = let
--   pf1 = LTZero_respects_Rel_helper_1 a b r
--   pf2 = LTZero_respects_Rel_helper_1 q p c
--   pf3 = plusCommutative (q * (S c)) (p * 0)
--   pf4 = trans (sym pf3) pf2
--   in
--   rewrite pf4 in (rewrite pf1 in Refl)

-- LTZero_respects_Rel_helper_3 : (a, b, r, p, q, c : Nat) -> 
--   (plus (plus (mult a 0) (mult b (S r))) (plus (mult p (S c)) (mult q 0))) = 
--   (plus (mult b (S r)) (mult p (S c)))

-- LTZero_respects_Rel_helper_3 a b r p q c = let
--   pf1 = LTZero_respects_Rel_helper_2 b a r q p c
--   pf2 = plusCommutative (a * 0) (b * (S r))
--   pf3 = plusCommutative (q * 0) (p * (S c))
--   pf4 = cong {f = (\x => (((b * (S r)) + (a * 0)) + x))} pf3
--   pf5 = cong {f = (\x => (x + ((p * (S c)) + (q * 0))))} pf2
--   in
--   trans (trans pf5 (sym pf4)) pf1

LTZero_respects_Rel : (a, b : Rational) -> (Rational_Rel a b) -> (LTEZero a) -> (LTEZero b)
LTZero_respects_Rel (a, b) (p, q) pfRel pfLTE = let
  pf1 = LTE_property_2 (S q)
  pf2 = LTE_property_2 (S b)
  in
  case (LTEZero_is_dec p) of
    (Yes pfLTE_p) => pfLTE_p
    (No contraLTE_p) => let
      pf3 = ZZ_plusCommutative a ZZ.zero -- a + 0 = 0 + a
      pf4 = ZZ_zero_is_additive_identity a -- 0 + a = a
      pf5 = trans pf3 pf4 -- a + 0 = a
      pf6 = ZZ_Rel_is_sym {x = (ZZ_plus a ZZ.zero)} {y = a} (Eq_implies_ZZ_Rel pf5) -- a ~  (a + 0) 
      pf7 = LTEZero_respects_ZZ_Rel a (ZZ_plus a ZZ.zero) pf6 pfLTE -- LTEZero (a + 0)
      pf8 = LTE_property_3 a ((S q), 0) pf7 pf1 -- LTE (a * (q + 1)) ZZ.zero
      pf9 = ZZ_plusCommutative (ZZ_mult a (S q, 0)) ZZ.zero -- (a * (q + 1)) + 0 = 0 + (a * (q + 1))  
      pf10 = ZZ_zero_is_additive_identity (ZZ_mult a (S q, 0)) -- 0 + (a * (q + 1)) = (a * (q + 1))
      pf11 = trans pf9 pf10 -- (a * (q + 1)) + 0 = (a * (q + 1))
      pf12 = (Eq_implies_ZZ_Rel pf11) -- (a * (q + 1)) + 0 ~ (a * (q + 1))    
      pf13 = LTEZero_respects_ZZ_Rel (ZZ_plus (ZZ_mult a (S q, 0)) 0) (ZZ_mult a (S q, 0)) pf12 pf8 
      --  LTEZero (ZZ_mult a (S q, 0))
      pf14 = LTEZero_respects_ZZ_Rel (ZZ_mult a (S q, 0)) (ZZ_mult p (S b, 0)) pfRel pf13
      pf15 = LTE_property_5 p contraLTE_p -- LTE ZZ.zero p
      pf16 = LTE_property_1 p ((S b), 0) pf15 pf2 -- LTE ZZ.zero (ZZ_mult p (S q, 0))  
    in
    ?rhs