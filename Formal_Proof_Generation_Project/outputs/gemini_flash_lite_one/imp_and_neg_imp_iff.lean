theorem imp_and_neg_imp_iff (p q : Prop) : (p → q) ∧ (¬p → q) ↔ q := by
  constructor
  · intro h
    cases Classical.em p with
    | inl hp => exact h.1 hp
    | inr hnp => exact h.2 hnp
  · intro hq
    exact ⟨fun _ => hq, fun _ => hq⟩