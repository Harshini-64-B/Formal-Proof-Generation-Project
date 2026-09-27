theorem by_cases {p q : Prop} (hpq : p → q) (hnpq : ¬p → q) : q := by
  cases Classical.em p with
  | inl hp => exact hpq hp
  | inr hnp => exact hnpq hnp