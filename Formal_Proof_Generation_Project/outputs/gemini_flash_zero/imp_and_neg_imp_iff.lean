theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  constructor
  · intro h
    by_cases hp : p
    · exact h.left hp
    · exact h.right hp
  · intro hq
    constructor
    · intro _
      exact hq
    · intro _
      exact hq