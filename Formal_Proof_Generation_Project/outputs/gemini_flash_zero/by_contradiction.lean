theorem by_contradiction {p : Prop} : (¬p → False) → p := by
  intro h
  cases Classical.em p with
  | inl hp => exact hp
  | inr hnp => exact False.elim (h hnp)