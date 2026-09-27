theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  · intro h
    by_cases ha : a
    · right
      intro hb
      exact h ⟨ha, hb⟩
    · left
      exact ha
  · rintro (ha | hb) ⟨ha', hb'⟩
    · exact ha ha'
    · exact hb hb'