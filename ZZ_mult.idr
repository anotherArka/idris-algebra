module ZZ_mult

import ZZ
import properties_of_Nat

%access public export
%access total

ZZ_mult : ZZ -> ZZ -> ZZ
ZZ_mult (a, b) (c, d) = (a*c + b*d, a*d + b*c)

ZZ_mult_unit_pf : (x : ZZ) -> ((ZZ_mult x ZZ.one) = x)
ZZ_mult_unit_pf (a, b) = rewrite (multCommutative a 0) in 
  (rewrite (multCommutative b 1) in 
  (rewrite (multCommutative b 0) in 
  (rewrite (multCommutative a 1) in 
  (rewrite (plusCommutative a 0) in 
  (rewrite (plusCommutative a 0) in 
  (rewrite (plusCommutative b 0) in Refl))))))

ZZ_mult_commutative : (x, y : ZZ) -> (ZZ_mult x y = ZZ_mult y x)  
ZZ_mult_commutative (a, b) (c, d) = rewrite (multCommutative a c) in 
  (rewrite (multCommutative b d) in 
  (rewrite (multCommutative a d) in
  (rewrite (multCommutative b c) in 
  (rewrite (plusCommutative (c * b) (d * a)) in Refl))))

ZZ_is_integral_domain_helper : (a, b, c, d : Nat) -> (ZZ_Rel (ZZ_mult (a, b) (c, d)) ZZ.zero) -> 
  (Either (ZZ_Rel (a, b) ZZ.zero) (ZZ_Rel (c, d) ZZ.zero))
ZZ_is_integral_domain_helper Z Z _ _ _ = Left Refl
ZZ_is_integral_domain_helper _ _ Z Z _ = Right Refl
ZZ_is_integral_domain_helper Z (S b) Z (S d) pfRel_mult = let
  pf1 = plusCommutative (mult b 0) 0 
  pf2 = multCommutative b 0
  pf3 = trans pfRel_mult (trans pf1 pf2)
  in 
  absurd pf3
ZZ_is_integral_domain_helper Z (S b) (S c) Z pfRel_mult = let
  pf1 = plusCommutative (mult b 0) 0 
  pf2 = multCommutative b 0
  pf3 = trans (sym pfRel_mult) (trans pf1 pf2)
  in
  absurd pf3
ZZ_is_integral_domain_helper Z (S b) (S c) (S d) pfRel_mult = let
  pf1 = Sn_eq_Sm_implies_n_eq_m _ _ pfRel_mult
  pf2 = plusCommutative (plus d (mult b (S d))) 0
  pf3 = plusCommutative (plus c (mult b (S c))) 0
  pf4 = trans (sym pf2) (trans pf1 pf3)
  pf5 = cong {f = S} pf4
  pf6 = trans (multCommutative (S d) (S b)) (trans pf5 (multCommutative (S b) (S c)))
  pf7 = cancellation_mult b (S d) (S c) pf6
  pf8 = cong {f = S} (plusCommutative d 0)  
  pf9 = cong {f = S} (plusCommutative c 0)
  pf10 = trans pf9 (trans (sym pf7) (sym pf8))
  in
  (Right pf10)
ZZ_is_integral_domain_helper (S a) Z Z (S d) pfRel_mult = let
  pf1 = plusCommutative (mult a 0) 0 
  pf2 = multCommutative a 0
  pf3 = plusCommutative (plus (mult a 0) 0) 0
  pf4 = trans pf3 (trans pf1 pf2)
  pf5 = trans (sym pf4) pfRel_mult  
  in
  absurd pf5
ZZ_is_integral_domain_helper (S a) Z (S c) Z pfRel_mult = let
  pf1 = plusCommutative (mult a 0) 0 
  pf2 = multCommutative a 0
  pf3 = plusCommutative (plus (mult a 0) 0) 0
  pf4 = trans pf3 (trans pf1 pf2)
  pf5 = trans pfRel_mult pf4  
  in
  absurd pf5
ZZ_is_integral_domain_helper (S a) Z (S c) (S d) pfRel_mult = let
  pf1 = Sn_eq_Sm_implies_n_eq_m _ _ pfRel_mult
  pf2 = plusCommutative (plus d (mult a (S d))) 0
  pf3 = plusCommutative (plus c (mult a (S c))) 0
  pf4 = plusCommutative (plus (plus d (mult a (S d))) 0) 0
  pf5 = plusCommutative (plus (plus c (mult a (S c))) 0) 0
  pf6 = trans pf4 pf2
  pf7 = trans pf5 pf3
  pf8 = trans (sym pf7) (trans pf1 pf6)
  pf9 = cong {f = S} pf8
  pf10 = trans (multCommutative (S c) (S a)) (trans pf9 (multCommutative (S a) (S d)))
  pf11 = cancellation_mult a (S c) (S d) pf10
  in 
  Right(
  (rewrite (plusCommutative c 0) in
  (rewrite (plusCommutative d 0) in pf11)))

