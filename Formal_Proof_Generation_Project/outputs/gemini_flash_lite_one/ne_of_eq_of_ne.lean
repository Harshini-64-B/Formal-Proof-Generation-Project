theorem ne_of_eq_of_ne {α : Sort*} {a b c : α} (h₁ : a = b) (h₂ : b ≠ c) : a ≠ c := by
  intro h
  rw [h₁] at h
  exact h₂ h