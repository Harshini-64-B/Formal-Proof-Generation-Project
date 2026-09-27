theorem Iff.and {a c b d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := by
  rw [h₁, h₂]