theorem of_not_not {a : Prop} : ¬¬a → a := by
  intro h
  by_contra h_not_a
  exact h h_not_a