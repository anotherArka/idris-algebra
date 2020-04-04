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

||| Proof that if a ~ b and a <= 0 then b = 0
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

||| Proof that if a >= 0 and b >= 0 then a * b >= 0
LTE_property_1 : (a, b : ZZ) -> (LTE ZZ.zero a) -> (LTE ZZ.zero b) -> (LTE ZZ.zero (ZZ_mult a b))
LTE_property_1 (a, Z) (c, d) LTEZero pf2 = rewrite (plusCommutative (mult a d) 0) in
  (rewrite (plusCommutative (mult a c) 0) in 
  LTE_property_3 _ _ _ pf2)

LTE_property_1 ((S a), (S b)) (c, d) (LTESucc pf1) pf2 = ?rhs1