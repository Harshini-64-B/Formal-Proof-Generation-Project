theorem eq_or_ne {α : Sort u_1} (x y : α) : x = y ∨ x ≠ y := by
  by_cases h : x = y
  · left
    exact h
  · right
    exact h