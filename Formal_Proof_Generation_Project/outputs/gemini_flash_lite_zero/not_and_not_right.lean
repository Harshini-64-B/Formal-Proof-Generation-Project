theorem not_and_not_right {a b : Prop} : ¬(a ∧ ¬b) ↔ a → b := by
  constructor
  · intro h ha
    by_contra hb
    exact h ⟨ha, hb⟩
  · intro h ⟨ha, hnb⟩
    exact hnb (h ha)