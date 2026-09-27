theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  constructor
  · intro h
    cases p with
    | intro hp => exact h.1 hp
    | intro hnp => exact h.2 hnp
  · intro h
    constructor
    · intro hp
      exact h
    · intro hnp
      exact h