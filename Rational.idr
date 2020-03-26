module Rational

import ZZ
import ZZ_implementations

%access public export
%access total

Rational : Type 
Rational = (ZZ, Nat)

zero : Rational
zero = (0, Z)

Rational_Rel : Rational -> Rational -> Type
Rational_Rel (p1, q1) (p2, q2) = ZZ_Rel (p1 * (S q2, 0)) (p2 * (S q1, 0)) 
