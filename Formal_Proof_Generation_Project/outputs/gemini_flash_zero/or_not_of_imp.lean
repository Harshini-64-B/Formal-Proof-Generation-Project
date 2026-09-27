theorem or_not_of_imp : (a → b) → b ∨ ¬a := by
  intro h
  by_cases ha : a
  · exact Or.inl (h ha)
  · exact Or.inr ha