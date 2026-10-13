theorem of_not_not {a : Prop} : ¬¬a → a := by
  by classical
  intro h
  cases Classical.em a with
  | inl ha => exact ha
  | inr hna => contradiction