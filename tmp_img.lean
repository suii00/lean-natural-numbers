import Mathlib.Data.Set.Basic
open Set
variable {α β : Type} {s : Set α} {f : α → β}
#check Set.image f s
#check Set.image_eq_range
#check Set.mem_image
#check Set.mem_image_of_mem
