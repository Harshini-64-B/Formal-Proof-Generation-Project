theorem by_contradiction {p : Prop} : (¬p → False) → p := by
  intro h
  by_contra hp
  exact h hp