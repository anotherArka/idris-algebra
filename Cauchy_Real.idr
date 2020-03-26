module Cauchy_Real

import ZZ
import Rational
import Useful_functions
import Rational_ord
import Rational_abs
import Rational_implementations

%access public export
%access total

Cauchy_condition : (rats : Stream Rational) -> Type
Cauchy_condition rats = (n : Nat) -> 
  (m : Nat ** 
  ((k : Nat) -> (LTE m k) -> 
  (Rational_ord.LT (abs ((pick k rats) - (pick m rats))) (one, n)))) 

Cauchy_Real : Type
Cauchy_Real = (rats : (Stream Rational) ** (Cauchy_condition rats))

