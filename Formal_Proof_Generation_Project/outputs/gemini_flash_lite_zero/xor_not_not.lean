theorem xor_not_not {a b : Prop} : Xor (¬a) ¬b ↔ Xor a b := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      by_contra hb
      exact h2 hb
    · left
      by_contra ha
      exact h1 ha
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · right
      exact ⟨h2, fun ha => ha h1⟩
    · left
      exact ⟨fun hb => hb h2, h1⟩