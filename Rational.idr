module Rational

import ZZ
import ZZ_implementations

%access public export
%access total

Rational : Type 
Rational = (ZZ, Nat)

