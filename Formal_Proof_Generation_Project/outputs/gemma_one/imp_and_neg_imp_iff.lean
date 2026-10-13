theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  constructor
  · intro h
    cases Classical.em p with
    | inl hp => exact h.left hp
    | inr hnp => exact h.right hnp
  · intro h
    exact ⟨fun _ => h, fun _ => h⟩