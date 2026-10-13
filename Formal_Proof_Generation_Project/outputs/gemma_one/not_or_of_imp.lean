theorem not_or_of_imp {a b : Prop} : (a → b) → ¬a ∨ b := by
  intro h
  by_cases ha : a
  · exact Or.inr (h ha)
  · exact Or.inl ha