import Mathlib

open Matrix

local infixl:75 " ⬝ " => Matrix.mul

#check fun (A B : Matrix (Fin 1) (Fin 1) ℝ) => A ⬝ B
