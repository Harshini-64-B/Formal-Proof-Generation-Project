theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  · intro h
    by_cases ha : a
    · right
      intro hb
      apply h
      exact ⟨ha, hb⟩
    · left
      exact ha
  · intro h hab
    rcases h with ha | hb
    · exact ha hab.1
    · exact hb hab.2