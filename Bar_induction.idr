module Bar_induction

import Data.Vect
import Useful_functions
import Subtype

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

data Natural_spread : Type where
-- A spread is given by a law on natural numbers such that
-- 1. It is decidable
-- 2. If (x :: xs) is accepted then xs is accepted
-- 3. If xs is accepted then there is at least one acceptable extension (x :: xs)
  Spread : (law : (n : Nat) -> (xs : Vect n Nat) -> Type) ->
         ((n : Nat) -> (xs : Vect n Nat) -> (Dec (law n xs))) ->
         ((n : Nat) -> (xs : Vect (S n) Nat) -> (law (S n) xs) -> (law n (tail xs))) ->
         ((n : Nat) -> (xs : Vect n Nat) -> (law n xs) -> (x : Nat ** (law (S n) (x :: xs)))) ->
         Natural_spread  

-- The Following gives easy ways to extract components from a spread 

law_of : Natural_spread -> (n : Nat) -> (xs : Vect n Nat) -> Type
law_of (Spread law _ _ _ ) = law

law_is_decidable : (spread : Natural_spread) -> (n : Nat) -> (xs : Vect n Nat) -> 
  (Dec (law_of spread n xs))
law_is_decidable (Spread _ dec_pf _ _) = dec_pf

law_goes_backward : (spread : Natural_spread) -> (n : Nat) -> (xs : Vect (S n) Nat) ->
  (law_of spread (S n) xs) -> (law_of spread n (tail xs))
law_goes_backward (Spread _ _ backward _ ) = backward

law_extendable : (spread : Natural_spread) -> (n : Nat) -> (xs : Vect n Nat) ->
  (law_of spread n xs) -> (x : Nat ** (law_of spread (S n) (x :: xs)))
law_extendable (Spread _ _ _ extendable_pf) = extendable_pf  

{- 
------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------
This part is commented out because it is difficult to work with---------------------------------
intefaces for our purpose.----------------------------------------------------------------------
------------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------------


||| For now we work only with the spread of natural numbers.
||| A spread is an way of accepting finite strings.
||| Given a vector we should able to tell whether there
||| is a stream in the spread extending it.
||| Also it should be possible to extend any non-null vector
interface Natural_spread (rule : (m : Nat) -> (Vect m Nat) -> Type) where 
  Backward : (l : Nat) -> (accepted : (Vect (S (S l)) Nat)) ->
    (rule (S (S l)) accepted) -> (rule (tail accepted))
  Forward  : (l : Nat) -> (accepted : (Vect (S l) Nat)) -> (rule (S l) accepted) -> 
    (k : Nat ** (rule (k :: accepted)))
  Is_proposition : (l : Nat) -> (accepted : Vect l Nat) -> (Prop (rule l accepted))  

Species_of_spread : (rule : (m : Nat) -> (Vect m Nat) -> Type) ->
    (Natural_spread rule) => (Stream Nat) -> Type
Species_of_spread rule sequence = (l : Nat) -> (rule (S l) (pick_upto (S l) sequence))     

||| Fan is the shorthand for finitary spread. 
||| Thinking a spread as a tree, it is called finitary if there are only finite possibilities
||| from which the spread can start, and finite ways to extend it. 
interface Natural_spread rule => Natural_fan (rule : (m : Nat) -> (Vect m Nat) -> Type) where
  Starts_finitly : (bound : Nat ** ((k : Nat) -> (LT bound k) -> (rule 1 (k :: Nil)) -> Void))
  Extends_finitly : (l : Nat) -> (accepted : Vect l Nat) -> (rule l accepted) -> 
    (bound : Nat ** ((k : Nat) -> (LT bound k) -> (rule (S l) (k :: accepted)) -> Void))
----------------------------------------------------------------------------------------------------------  
interface (Natural_spread rule) => 
  Natural_bar (rule : (m : Nat) -> (Vect m Nat) -> Type) 
    (species : (m : Nat) -> (el : Vect m Nat) -> (rule el) -> Type) where

  Is_decidable : (m : Nat) -> (el : Vect m Nat) -> (inside : rule m el) -> 
    (Dec (species m el inside))
  Is_bar : (sequence : Stream Nat) -> (Species_of_spread rule sequence)
-}  