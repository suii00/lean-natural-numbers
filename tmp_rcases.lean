import Mathlib.Data.Set.Basic
open Set
variable {α β : Type} {s : Set α} {f : α → β} {b : β}
#check (by
  intro hb
  rcases hb with ⟨a, ha, rfl⟩
  )
