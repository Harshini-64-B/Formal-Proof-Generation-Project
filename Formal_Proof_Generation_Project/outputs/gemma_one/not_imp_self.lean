theorem not_imp_self {a : Prop} : ¬a → (a ↔ a) := by
  intro h
  exact Iff.rfl