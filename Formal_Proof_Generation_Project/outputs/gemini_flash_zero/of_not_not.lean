theorem of_not_not {a : Prop} : ¬¬a → a := by
  intro h
  exact Classical.byContradiction h