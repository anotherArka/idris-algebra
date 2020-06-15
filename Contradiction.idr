module Contradiction

data Paradox = Loop (Paradox -> Void)

contradiction : Paradox -> Void
contradiction (Loop el) = el (Loop el)

boom : Void
boom = contradiction (Loop contradiction)