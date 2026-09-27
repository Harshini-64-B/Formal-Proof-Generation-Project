theorem or_not {p : Prop} : p ∨ ¬p := by
  by_cases h : p
  · exact Or.inl h
  · exact Or.inr h