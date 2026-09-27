theorem not_ne_iff {α : Sort u_1} {a b : α} : ¬a ≠ b ↔ a = b := by
  exact Classical.not_not