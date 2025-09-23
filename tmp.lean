import Mathlib

lemma test (a b c d : ℤ) :
  (↑a + ↑b * Real.sqrt 2) * (↑c + ↑d * Real.sqrt 2)
      = (↑a * ↑c) + (↑a * ↑d + ↑b * ↑c) * Real.sqrt 2 + ↑b * ↑d * ((Real.sqrt 2) ^ 2) := by
  ring

