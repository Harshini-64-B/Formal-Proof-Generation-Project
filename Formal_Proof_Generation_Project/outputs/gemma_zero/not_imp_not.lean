theorem not_imp_not {a b : Prop} : ¬a → ¬b ↔ b → a := by
  constructor
  · intro h b not_a
    cases h not_a b
  · intro h not_a b
    cases h b not_a