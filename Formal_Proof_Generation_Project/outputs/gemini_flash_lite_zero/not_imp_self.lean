theorem not_imp_self {a : Prop} : ¬a → (a ↔ a) := by
  intro _
  exact Iff.rfl