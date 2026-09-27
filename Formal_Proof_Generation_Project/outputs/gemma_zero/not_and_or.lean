theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  · intro h
    by_contra h'
    apply h
    constructor
    · intro ha <;> apply h' <;> left <;> exact ha
    · intro hb <;> apply h' <;> right <;> exact hb
  · intro h
    intro h_and
    cases h <;> (match h with | Or.inl ha => exact ha (And.left h_and) | Or.inr hb => exact hb (And.right h_and))