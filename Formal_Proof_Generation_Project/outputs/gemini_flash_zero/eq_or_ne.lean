theorem eq_or_ne {α : Sort u_1} (x y : α) : x = y ∨ x ≠ y :=
  Classical.em (x = y)