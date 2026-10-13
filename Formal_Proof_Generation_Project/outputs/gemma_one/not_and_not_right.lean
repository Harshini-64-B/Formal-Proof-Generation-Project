theorem not_and_not_right {a b : Prop} : ¬(a ∧ ¬b) ↔ a → b := by
  constructor
  · intro h ha
    cases Classical.em b with
    | inl hb => exact hb
    | inr hnb => exact (h ⟨ha, hnb⟩).elim
  · intro h
    intro h_and
    cases h_and with
    | intro ha hnb => exact hnb (h ha)