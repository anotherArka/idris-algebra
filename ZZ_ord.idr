module ZZ_ord

import properties_of_Nat
import Useful_functions
import ZZ
import ZZ_plus
import ZZ_minus
import ZZ_mult

%access public export
%access total

ZZ_greater_than_zero_helper : Nat -> Nat -> Bool
ZZ_greater_than_zero_helper Z n = False
ZZ_greater_than_zero_helper (S m) Z = True
ZZ_greater_than_zero_helper (S m) (S n) = ZZ_greater_than_zero_helper m n

LTEZero : ZZ -> Type
LTEZero (a, b) = LTE a b

||| Proof that LTZero is decidable
LTEZero_is_dec : (a : ZZ) -> (Dec (LTEZero a))
LTEZero_is_dec (a, b) = LTE_is_dec a b

ZZ_greater_than_zero : ZZ -> Bool
ZZ_greater_than_zero (a, b) = ZZ_greater_than_zero_helper a b

ZZ_strict_order : ZZ -> ZZ -> Bool
ZZ_strict_order a b = ZZ_greater_than_zero (ZZ_minus a b)

LTE : ZZ -> ZZ -> Type
LTE a b = LTEZero (ZZ_minus a b)

||| Proof that LT is decidable
LTE_is_dec : (a, b : ZZ) -> (Dec (LTE a b))
LTE_is_dec a b = LTEZero_is_dec _

||| Proof that if a ~ b and a <= 0 then b <= 0
LTEZero_respects_ZZ_Rel : (a, b : ZZ) -> (ZZ_Rel a b) -> (LTEZero a) -> (LTEZero b)
LTEZero_respects_ZZ_Rel (a, b) (c, d) pfRel pfLTE = let
  pf1 = LTE_property_1 a b d pfLTE
  pf2 = plusCommutative d a
  pf3 = plusCommutative b c
  pf4 = trans pf2 (trans pfRel pf3)
  pf5 = Family_respects_eq {f = (\x => (LTE x (d + b)))} pf4 pf1
  pf6 = Family_respects_eq {f = (\x => (LTE x (d + b)))} (plusCommutative c b) pf5
  pf7 = Family_respects_eq {f = (\x => LTE (b + c) x)} (plusCommutative d b) pf6
  pf8 = LTE_property_2 c d b pf7
  in
  pf8

LTE_is_refl : LTE ZZ.zero ZZ.zero
LTE_is_refl = LTEZero

||| Proof that if a >= 0 and b >= 0 then a * b >= 0
LTE_property_1 : (a, b : ZZ) -> (LTE ZZ.zero a) -> (LTE ZZ.zero b) -> (LTE ZZ.zero (ZZ_mult a b))
LTE_property_1 (a, Z) (c, d) LTEZero pf2 = rewrite (plusCommutative (mult a d) 0) in
  (rewrite (plusCommutative (mult a c) 0) in 
  LTE_property_3 _ _ _ pf2)
LTE_property_1 ((S a), (S b)) (c, d) (LTESucc pf1) pf2 = let
  induct_hyp = LTE_property_1 (a, b) (c, d)  pf1 pf2
  pf = LTE_property_1 _ _ (d + c) induct_hyp -- this one is from properties of nat
  in
   rewrite (adding_four_3 d (a * d) c (b * c)) in 
  (rewrite (adding_four_3 c (a * c) d (b * d)) in 
  (rewrite (plusCommutative c d) in pf))

|||Proof that (q, 0) >= 0
LTE_property_2 : (n : Nat) -> (LTE ZZ.zero (n , 0))
LTE_property_2 Z = LTEZero
LTE_property_2 (S k) = LTEZero

||| Proof that if a <= 0 and b >= 0 then a * b <= 0
LTE_property_3 : (a, b : ZZ) -> (LTE a ZZ.zero) -> (LTE ZZ.zero b) -> (LTE (ZZ_mult a b) ZZ.zero)
LTE_property_3 (a, b) (c, d) pf1 pf2 = 
  let
  pf3 = Family_respects_eq {f = (\x => (LTE x (b + 0)))} (plusCommutative a 0) pf1
  pf4 = Family_respects_eq {f = (\x => (LTE a x))} (plusCommutative b 0) pf3
  pf5 = LTE_property_1 (b, a) (c, d) pf4 pf2
  in
   rewrite (plusCommutative ((a * c) + (b * d)) 0) in
  (rewrite (plusCommutative ((a * d) + (b * c)) 0) in 
  (rewrite (plusCommutative (a * c) (b * d)) in 
  (rewrite (plusCommutative (a * d) (b * c)) in pf5)))

||| Proof that if (a >= 0) leads to a contradiction then (a <= 0) and (not (a = 0))
LTE_property_4 : (a : ZZ) -> ((LTE ZZ.zero a) -> Void) -> ((LTEZero a), (ZZ_Rel a ZZ.zero) -> Void)
LTE_property_4 (a, b) contraLTE = ((LTE_property_5 a b contraLTE), \pf =>
  let
  pf1 = trans (plusCommutative Z a) (trans pf (plusCommutative b Z)) 
  pf2 = LTEZero_respects_ZZ_Rel ZZ.zero (b, a) pf1 LTE_is_refl  
  in
  (contraLTE pf2))

||| Proof that if (a <= 0) leads to a contradiction then (a >= 0) and (not (a = 0))
LTE_property_5 : (a : ZZ) -> ((LTEZero a) -> Void) -> ((LTE ZZ.zero a), (ZZ_Rel a ZZ.zero) -> Void)
LTE_property_5 (a, b) contraLTE = (LTE_property_5 b a contraLTE, \pf =>
  let
  pf1 = sym (trans (plusCommutative Z a) (trans pf (plusCommutative b Z))) 
  pf2 = LTEZero_respects_ZZ_Rel ZZ.zero (a, b) pf1 LTE_is_refl
  in
  (contraLTE pf2))

||| Proof that if a <= b and b <= a then a = b
LTE_property_6 : (x, y : ZZ) -> (LTE x y) -> (LTE y x) -> (ZZ_Rel x y)
LTE_property_6 (a, b) (c, d) pf_xy pf_yx = let
  pf1 = Family_respects_eq {f = (\x => (LTE (c + b) x))} (plusCommutative d a) pf_yx
  pf2 = Family_respects_eq {f = (\x => (LTE x (a + d)))} (plusCommutative c b) pf1
  in
  (LTE_property_7 _ _ pf_xy pf2)