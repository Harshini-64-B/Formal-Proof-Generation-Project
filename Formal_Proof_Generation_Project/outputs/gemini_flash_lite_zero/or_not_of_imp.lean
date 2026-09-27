theorem or_not_of_imp : (a → b) → b ∨ ¬a := by
  intro h
  by_cases ha : a
  · left
    exact h ha
  · right
    exact ha