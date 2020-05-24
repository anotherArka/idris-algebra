module Intuitionistic_theorems

half_double_negation : {ty : Type} -> ty -> ((ty -> Void) -> Void)
half_double_negation a f = f a

weak_contrapositive : {u, v : Type} -> (u -> v) -> (v -> Void) -> (u -> Void)
weak_contrapositive f g a = g (f a)

weak_double_negation : {ty : Type} -> (((ty -> Void) -> Void) -> Void) -> (ty -> Void)
weak_double_negation {ty = ty} = weak_contrapositive {u = ty} {v = ((ty -> Void) -> Void)} 
  half_double_negation
