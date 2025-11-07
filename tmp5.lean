import Mathlib.Data.Fin.Basic

example : (1 : Fin 4) ≤ 2 := by decide

example : (1 : Fin 4) ≤ 2 := by
  have h : (1 : Fin 4) ≤ 2 := by decide
  simpa using h
