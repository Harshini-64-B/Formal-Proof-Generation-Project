theorem Iff.and {a c b d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := by
  constructor
  . intro h
    exact ⟨h₁.mp h.left, h₂.mp h.right⟩
  . intro h
    exact ⟨h₁.mpr h.left, h₂.mpr h.right⟩