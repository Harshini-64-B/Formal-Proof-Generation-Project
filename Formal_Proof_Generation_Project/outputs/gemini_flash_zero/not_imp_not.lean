theorem not_imp_not {a b : Prop} : (¬a → ¬b) ↔ (b → a) := by
  constructor
  · intro h hb
    by_contra hna
    exact h hna hb
  · intro h hna hb
    exact hna (h hb)