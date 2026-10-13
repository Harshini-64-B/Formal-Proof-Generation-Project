theorem of_not_imp {a b : Prop} : ¬(a → b) → a := by
  intro h
  by contra h_na
  apply h
  intro x
  exact (h_na x).elim
  exact h_na