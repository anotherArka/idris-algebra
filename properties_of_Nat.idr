module properties_of_Nat

%access public export
%access total

Z_is_not_Sn : (n : Nat) -> ((S n) = Z) -> Void
Z_is_not_Sn n Refl impossible

n_eq_m_implies_Sn_eq_Sm : (n : Nat) -> (m : Nat) -> (n = m) -> ((S n) = (S m))
n_eq_m_implies_Sn_eq_Sm n m prf = cong prf

Sn_eq_Sm_implies_n_eq_m : (n : Nat) -> (m : Nat) -> (S n) = (S m) -> (n = m)
Sn_eq_Sm_implies_n_eq_m n n Refl = Refl

cancellation : (k : Nat) -> (a : Nat) -> (b : Nat) -> (plus k a = plus k b) -> (a = b)
cancellation Z a b prf = prf
cancellation (S k) a b prf = cancellation k a b (Sn_eq_Sm_implies_n_eq_m (plus k a) (plus k b) prf)	 

adding_four_1 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> plus (plus a b) (plus k l) = plus a (plus b (plus k l))
adding_four_1 a b k l = sym (plusAssociative a b (plus k l))
                          
adding_four_2 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> plus (plus a b) (plus k l) = plus (plus k b) (plus l a)
adding_four_2 a b k l = rewrite (sym (plusAssociative a b (plus k l))) in 
  (rewrite (plusAssociative b k l) in 
  (rewrite (plusAssociative a (plus b k) l) in 
  (rewrite (plusCommutative a (plus b k)) in 
  (rewrite (sym (plusAssociative (plus b k) a l)) in 
  (rewrite (plusCommutative b k) in
  (rewrite (plusCommutative a l) in Refl))))))

adding_four_3 : (a, b, c, d : Nat) -> (((a + b) + (c + d)) = ((a + c) + (b + d)))
adding_four_3 a b c d = rewrite (adding_four_1 a b c d) in 
  (rewrite (plusAssociative b c d) in 
  (rewrite (plusCommutative b c) in 
  (rewrite (sym (plusAssociative c b d)) in  
  (rewrite (adding_four_1 a c b d) in Refl))))

adding_equal_to_both_sides : (a, b, c, d : Nat) -> (a = b) -> (c = d) -> ((a + c) = (b + d))
adding_equal_to_both_sides a a c c Refl Refl = Refl

-- public export
 	
-- multiplying_four_1 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> mult (mult a b) (mult k l) = mult a (mult b (mult k l))
-- multiplying_four_1 a b k l = rewrite symmetry (associativeMult (mult a b) k l) in 
--                             (rewrite associativeMult a b k in 
--                             (rewrite associativeMult a (mult b k) l in 
--                             (rewrite symmetry (associativeMult b k l) in Refl)))
                            
-- public export
                            
-- multiplying_four_2 : (a : Nat) -> (b : Nat) -> (k : Nat) -> (l : Nat) -> mult (mult a b) (mult k l) = mult (mult k b) (mult l a)
-- multiplying_four_2 a b k l = rewrite (multiplying_four_1 a b k l) in 
--                        (rewrite (commutativeMult l a) in 
--                        (rewrite (commutativeMult k b) in 
--                        (rewrite (multiplying_four_1 b k a l) in 
--                        (rewrite symmetry (associativeMult k a l) in 
--                        (rewrite (commutativeMult k a) in 
--                        (rewrite (associativeMult a k l) in 
--                        (rewrite symmetry (multiplying_four_1 a b k l) in 
--                        (rewrite symmetry (multiplying_four_1 b a k l) in 
--                        (rewrite (commutativeMult a b) in Refl)))))))))          	
                            
