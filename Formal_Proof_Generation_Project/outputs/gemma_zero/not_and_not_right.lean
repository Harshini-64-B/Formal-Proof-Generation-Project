theorem not_and_not_right {a b : Prop} : ¬(a ∧ ¬b) ↔ a → b := by
  constructor
  · intro h a hb
    exfalso
    exact h ⟨a, hb⟩
  · intro h a hb
    exact hb (h a)