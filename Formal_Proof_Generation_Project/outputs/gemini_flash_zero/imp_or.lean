theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) := by
  constructor
  · intro h
    by_cases ha : a
    · cases h ha with
      | inl hb => exact Or.inl (fun _ => hb)
      | inr hc => exact Or.inr (fun _ => hc)
    · exact Or.inl (fun ha' => False.elim (ha ha'))
  · intro h ha
    cases h with
    | inl hab => exact Or.inl (hab ha)
    | inr hac => exact Or.inr (hac ha)