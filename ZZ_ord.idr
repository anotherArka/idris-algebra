module ZZ_ord

import properties_of_Nat
import ZZ
import ZZ_minus

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
