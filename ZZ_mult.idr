module ZZ_mult

import Useful_functions
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

ZZ_mult_associative : (x, y, z : ZZ) -> (ZZ_Rel (ZZ_mult x (ZZ_mult y z)) (ZZ_mult (ZZ_mult x y) z))
ZZ_mult_associative (a, b) (c, d) (p, q) = rewrite (distributive_left a (c * p) (d * q)) in 
  (rewrite (distributive_left b (c * q) (d * p)) in 
  (rewrite (distributive_right (a * c) (b * d) q) in 
  (rewrite (distributive_right (a * d) (b * c) p) in 
  (rewrite (distributive_left a (c * q) (d * p)) in 
  (rewrite (distributive_left b (c * p) (d * q)) in 
  (rewrite (distributive_right (a * c) (b * d) p) in 
  (rewrite (distributive_right (a * d) (b * c) q) in 
  (rewrite (multAssociative a c p) in 
  (rewrite (multAssociative a d q) in 
  (rewrite (multAssociative b c q) in 
  (rewrite (multAssociative b d p) in 
  (rewrite (multAssociative a c q) in 
  (rewrite (multAssociative a d p) in
  (rewrite (multAssociative b c p) in 
  (rewrite (multAssociative b d q) in
  (rewrite (adding_eight_1 ((a * c) * p) ((a * d) * q) ((b * c) * q) ((b * d) * p)
                           ((a * c) * q) ((b * d) * q) ((a * d) * p) ((b * c) * p)) 
    in Refl ))))))))))))))))
  
ZZ_mult_wrt_rel_helper_helper : (a, b, c, d, m, n : Nat) -> ((a + d) = (b + c)) ->
  (((a * m) + (b * n)) + ((c * n) + (d * m)) = (d + a) * (n + m))
ZZ_mult_wrt_rel_helper_helper a b c d m n pfRel = let
  pf1 =  adding_four_2 (a * m) (b * n) (c * n) (d * m)
  pf2 = trans (plusCommutative d a) (trans pfRel (plusCommutative b c))
  pf3 = sym (distributive_right c b n)
  pf4 = sym (distributive_right d a m)
  pf5 = cong {f = (\x => (x * n))} pf2
  pf6 = cong {f = (\x => (x * m))} pf2
  pf7 = cong {f = (\x => (x + ((d * m) + (a * m))))} pf3
  pf8 = cong {f = (\x => (((c + b) * n) + x))} pf4
  pf9 = trans pf7 pf8
  pf10 = cong {f = (\x => (x + ((d + a) * m)))} (sym pf5)
  pf11 = sym (distributive_left (d + a) n m)
  pf12 = trans pf1 (trans pf7 (trans pf8 (trans pf10 pf11)))
  in
  pf12


ZZ_mult_wrt_rel_helper : (a, b, c : ZZ) -> (ZZ_Rel a b) -> (ZZ_Rel (ZZ_mult a c) (ZZ_mult b c))
ZZ_mult_wrt_rel_helper (a, b) (c, d) (m, n) pfRel = let
  pf1 = ZZ_mult_wrt_rel_helper_helper a b c d m n pfRel
  pf2 = ZZ_mult_wrt_rel_helper_helper a b c d n m pfRel
  pf3 = cong {f = (\x => ((d + a) * x))} (plusCommutative n m)
  in
  (trans pf1 (trans pf3 (sym pf2)))

||| Proof that ZZ_mult respects ZZ_Rel
ZZ_mult_wrt_rel : (a, b, c, d : ZZ) -> (ZZ_Rel a b) -> (ZZ_Rel c d) -> (ZZ_Rel (ZZ_mult a c) (ZZ_mult b d))
ZZ_mult_wrt_rel a b c d pfRel_ab pfRel_cd = let
  pf1 = ZZ_mult_wrt_rel_helper a b c pfRel_ab
  pf2 = Eq_implies_ZZ_Rel (ZZ_mult_commutative b c)
  pf3 = ZZ_mult_wrt_rel_helper c d b pfRel_cd
  pf4 = Eq_implies_ZZ_Rel (ZZ_mult_commutative d b)
  in
  ZZ_Rel_is_trans pf1
  (ZZ_Rel_is_trans pf2
  (ZZ_Rel_is_trans pf3 pf4))

||| Helper to prove that if a * b ~ 0 then either a ~ 0 or b ~ 0
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
ZZ_is_integral_domain_helper (S a) (S b) Z (S d) pfRel_mult = let
  pf1 = plusCommutative (plus (mult a 0) (S (plus d (mult b (S d))))) 0
  pf2 = plusCommutative (mult a 0) (S (plus d (mult b (S d))))
  pf3 = cong {f = (\x => (x + (S (plus d (mult b (S d))))))} (multCommutative a 0)
  pf4 = cong {f = S} (plusCommutative  (plus (plus d (mult a (S d))) (mult b 0)) 0)
  pf5 = cong {f = (\x => (S (plus (plus d (mult a (S d))) x)))} (multCommutative b 0)
  pf6 = cong {f = S} (plusCommutative (plus d (mult a (S d))) 0)
  pf7 = trans pfRel_mult (trans pf4 (trans pf5 pf6))
  pf8 = trans pf1 pf3
  pf9 = (trans (sym pf8) pf7)
  pf10 = sym (cancellation_mult d (S b) (S a) pf9)
  in
  Left (rewrite (plusCommutative a 0) in
       (rewrite (plusCommutative b 0) in pf10)) 
ZZ_is_integral_domain_helper (S a) (S b) (S c) Z pfRel_mult = let
  pf1 = plusCommutative (plus (plus c (mult a (S c))) (mult b 0)) 0
  pf2 = cong {f = (\x => (plus (plus c (mult a (S c))) x))} (multCommutative b 0)
  pf3 = plusCommutative (plus c (mult a (S c))) 0
  pf4 = cong {f = S} (trans pf1 (trans pf2 pf3))
  pf5 = plusCommutative (plus (mult a 0) (S (plus c (mult b (S c))))) 0
  pf6 = cong {f = (\x => (x + (S (plus c (mult b (S c))))))} (multCommutative a 0)
  pf7 = trans pf5 pf6
  pf8 = trans (sym pf4) (trans pfRel_mult pf7)
  pf9 = cancellation_mult c (S a) (S b) pf8 
  in
  Left (rewrite (plusCommutative a 0) in
       (rewrite (plusCommutative b 0) in pf9))
ZZ_is_integral_domain_helper (S a) (S b) (S c) (S d) pfRel_mult = let
  pf1 = plusCommutative (plus (plus c (mult a (S c))) (S (plus d (mult b (S d))))) 0
  pf2 = cong {f = S} pf1
  pf3 = plusCommutative (plus (plus d (mult a (S d))) (S (plus c (mult b (S c))))) 0
  pf4 = cong {f = S} pf3
  pf5 = Sn_eq_Sm_implies_n_eq_m _ _ (trans (sym pf2) (trans pfRel_mult pf4))
  pf6 = plusCommutative (plus d (mult a (S d))) (S (plus c (mult b (S c))))
  pf7 = plusCommutative (plus c (mult a (S c))) (S (plus d (mult b (S d))))
  pf8 = trans (sym pf7) (trans pf5 pf6)
  pf9 = Sn_eq_Sm_implies_n_eq_m _ _ pf8
  pf10 = plusCommutative (plus d (mult b (S d))) (plus c (mult a (S c)))
  pf11 = plusAssociative c (mult a (S c)) (plus d (mult b (S d)))
  pf12 = plusAssociative c (mult b (S c)) (plus d (mult a (S d)))
  pf13 = trans pf12 (trans (sym pf9) (trans pf10 (sym pf11)))
  pf14 = cancellation c (plus (mult b (S c)) (plus d (mult a (S d)))) 
                        (plus (mult a (S c)) (plus d (mult b (S d)))) pf13
  pf15 = plusCommutative (mult b (S c)) (plus d (mult a (S d)))
  pf16 = plusCommutative (mult a (S c)) (plus d (mult b (S d)))
  pf17 = trans (sym pf15) (trans pf14 pf16)
  pf18 = plusAssociative d (mult a (S d)) (mult b (S c))
  pf19 = plusAssociative d (mult b (S d)) (mult a (S c))
  pf20 = trans pf18 (trans pf17 (sym pf19))
  pf21 = cancellation d (plus (mult a (S d)) (mult b (S c))) 
                        (plus (mult b (S d)) (mult a (S c))) pf20
  pf22 = plusCommutative (mult a (S d)) (mult b (S c))
  pf23 = plusCommutative (mult b (S d)) (mult a (S c))
  pf24 = sym (trans pf21 pf23)
  pf26 = ZZ_is_integral_domain_helper a b (S c) (S d) 
    (trans (plusCommutative (plus (mult a (S c)) (mult b (S d))) 0) 
    (trans pf24
    (plusCommutative 0 (plus (mult a (S d)) (mult b (S c))))))                      
  in
  case pf26 of
    Right pf => Right pf
    Left pf => Left (cong {f = S} pf)



ZZ_is_integral_domain : (x, y : ZZ) -> (ZZ_Rel (ZZ_mult x y) ZZ.zero) -> 
  (Either (ZZ_Rel x ZZ.zero) (ZZ_Rel y ZZ.zero))
ZZ_is_integral_domain (a, b) (c, d) pf = ZZ_is_integral_domain_helper a b c d pf

multiplying_four_1 : (a, b, c, d : ZZ) -> (ZZ_Rel 
  (ZZ_mult (ZZ_mult a b) (ZZ_mult c d))  
  (ZZ_mult (ZZ_mult a d) (ZZ_mult c b))) 
multiplying_four_1 a b c d = let 
  
  in
  ?rhs_ZZ_multiplying_four_1