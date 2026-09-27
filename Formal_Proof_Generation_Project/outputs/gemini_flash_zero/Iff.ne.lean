theorem Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) := by
  intro h
  exact not_congr h