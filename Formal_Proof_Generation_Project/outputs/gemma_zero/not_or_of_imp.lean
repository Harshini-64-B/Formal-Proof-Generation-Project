theorem not_or_of_imp {a b : Prop} : (a → b) → ¬a ∨ b := by
  intro h
  cases Classical.em a with
  | inl ha => exact Or.inr (h ha)
  | inr hna => exact Or.inl hna