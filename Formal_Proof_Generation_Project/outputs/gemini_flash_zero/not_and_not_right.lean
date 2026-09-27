theorem not_and_not_right {a b : Prop} : ¬(a ∧ ¬b) ↔ a → b := by
  constructor
  · intro h ha
    apply Classical.byContradiction
    intro hnb
    exact h ⟨ha, hnb⟩
  · intro h ⟨ha, hnb⟩
    exact hnb (h ha)