theorem Iff.ne {α β : Sort*} {a b : α} {c d : β} : (a = b ↔ c = d) → (a ≠ b ↔ c ≠ d) := by
  intro h
  constructor
  · intro h_neq
    rw [h] at h_neq
    exact h_neq
  · intro h_neq
    rw [h] at h_neq
    exact h_neq