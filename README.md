# idris-algebra
Formalization of algebra in Idris.

### Current Work
Currently I am developing integers and rationals so I can start work with
reals.

## Integers 
I have defined integers as the type of pairs of natural numbers and a relation between them.
Then I have defined multiple operatiions on them and shown that they respect the relations.

## Rationals
I have defined rationals as the pair (Integer, Natural) and a relation between them. In the 
reprsentation ``(a, b)`` corresponds to the rational number $$\frac{a}{b + 1}$$.
Then I have defined multiple operations on them and shown that they respect the relations.

## Reals
I have defined reals as streams of rational number satisfying cauchy condition.
A lot work has to be done about integers and rationals to work with them. 
