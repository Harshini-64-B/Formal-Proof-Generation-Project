theorem Iff.and {a c b d : Prop} (h₁ : a ↔ c) (h₂ : b ↔ d) : a ∧ b ↔ c ∧ d := by
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨h₁.mp ha, h₂.mp hb⟩
  · rintro ⟨hc, hd⟩
    exact ⟨h₁.mpr hc, h₂.mpr hd⟩