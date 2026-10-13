theorem not_or_of_imp {a b : Prop} : (a → b) → ¬a ∨ b := by
  intro h
  by_cases ha : a
  · right
    exact h ha
  · left
    exact ha