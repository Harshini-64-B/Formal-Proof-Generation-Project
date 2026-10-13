theorem not_imp_not {a b : Prop} : ¬a → ¬b ↔ b → a := by
  constructor
  · intro h ha hb
    exact h ha hb
  · intro h ha hb
    exact ha (h hb)