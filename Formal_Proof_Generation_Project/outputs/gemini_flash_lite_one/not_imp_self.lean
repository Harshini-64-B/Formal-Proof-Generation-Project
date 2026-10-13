theorem not_imp_self {a : Prop} : ¬a → (a ↔ a) := by
  intro _
  constructor
  · intro h; exact h
  · intro h; exact h