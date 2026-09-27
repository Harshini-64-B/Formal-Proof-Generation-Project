theorem or_not_of_imp (a b : Prop) (h : a → b) : b ∨ ¬a := by
  by_cases ha : a
  · left
    exact h ha
  · right
    exact ha