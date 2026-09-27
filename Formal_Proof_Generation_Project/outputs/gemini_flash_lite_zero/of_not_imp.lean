theorem of_not_imp {a b : Prop} : ¬(a → b) → a := by
  intro h
  by_contra ha
  apply h
  intro ha'
  exact (ha ha').elim