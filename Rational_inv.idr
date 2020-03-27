module Rational_inv

import ZZ_implementations
import Rational
import Rational_plus 

%access public export
%access total

Rational_inv : Rational -> Rational
Rational_inv (a, b) = (-a, b)

Rational_inv_pf : (rat : Rational) -> (Rational_Rel (Rational_plus rat (Rational_inv rat)) Rational.zero)
Rational_inv_pf ((a, b), q) = rewrite (multCommutative b 0) in 
  (rewrite (multCommutative a 0) in 
  (rewrite (plusCommutative (mult a (S q)) 0) in 
  (rewrite (plusCommutative (mult b (S q)) 0) in 
  (rewrite (multCommutative (plus (mult b (S q)) (mult a (S q))) 0) in   
  (rewrite (multCommutative (plus (mult a (S q)) (mult b (S q))) 0) in 
  (rewrite (multCommutative (plus (mult b (S q)) (mult a (S q))) 1) in 
  (rewrite (multCommutative (plus (mult a (S q)) (mult b (S q))) 1) in 
  (rewrite (plusCommutative (plus (mult a (S q)) (mult b (S q))) 0) in 
  (rewrite (plusCommutative (plus (mult a (S q)) (mult b (S q))) 0) in 
  (rewrite (plusCommutative (plus (mult a (S q)) (mult b (S q))) 0) in 
  (rewrite (plusCommutative (plus (mult b (S q)) (mult a (S q))) 0) in 
  (rewrite (plusCommutative (plus (mult b (S q)) (mult a (S q))) 0) in 
  (rewrite (plusCommutative (mult b (S q)) (mult a (S q))) in Refl)))))))))))))