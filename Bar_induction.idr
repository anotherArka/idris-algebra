module Bar_induction

import Data.Vect
import Useful_functions

-- %access public export
-- %access total

||| Functions on (stream dom).
||| Representing the fact that for any n : Nat the n-th element of the output
||| should be computable using only a finite subset of the infinite data.
Stream_function_type : (dom, cod : Type) -> Type
Stream_function_type dom cod = (n : Nat) -> (m : Nat ** ((Vect m dom) -> cod))

||| Applies a stream function on a stream to get a stream
apply : {dom, cod : Type} -> (str_f : Stream_function_type dom cod)  -> (st : Stream dom) -> (Stream cod)
apply str_f st = let
  m = fst (str_f Z) -- length of the required part to calculate the first value
  f_head = snd (str_f Z)
  req = pick_upto m st 
  f_tail = (\n => (str_f (S n)))
  in
  (f_head req) :: (apply f_tail st)

||| For now we work only with the spread of natural numbers.
||| A spread is an way of accepting finite strings.
||| Given a vector we should able to tell whether there
||| is a stream in the spread extending it.
||| Also it should be possible to extend any non-null vector
interface Natural_spread (rule : {m : Nat} -> (Vect m Nat) -> Type) where 
  Backward : {l : Nat} -> (accepted : (Vect (S l) Nat)) -> (rule accepted) -> (rule (tail accepted))
  Forward  : {l : Nat} -> (accepted : (Vect (S l) Nat)) -> (rule accepted) -> 
    (k : Nat ** (rule (k :: accepted)))                                    
      