theorem of_not_not {a : Prop} : ¬¬a → a := by
  intro h
  by_contra ha
  exact h ha