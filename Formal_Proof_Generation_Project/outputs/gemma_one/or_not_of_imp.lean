theorem or_not_of_imp {a b : Prop} : (a → b) → b ∨ ¬a := by
  intro h
  cases Classical.em a with
  | inl ha => left; exact h ha
  | inr hna => right; exact hna