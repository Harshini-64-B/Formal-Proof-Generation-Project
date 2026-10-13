theorem or_not {p : Prop} : p ∨ ¬p := by
  by_cases h : p
  · left
    exact h
  · right
    exact h