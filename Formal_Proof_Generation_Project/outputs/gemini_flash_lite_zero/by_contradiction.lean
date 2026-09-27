theorem by_contradiction {p : Prop} : (¬p → False) → p := by
  intro h
  by_cases hp : p
  · exact hp
  · exfalso
    exact h hp