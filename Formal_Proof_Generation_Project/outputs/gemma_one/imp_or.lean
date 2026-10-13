theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) := by
  constructor
  · intro h
    cases Classical.em (a → b) with
    | inl h1 => exact Or.inl h1
    | inr h2 =>
      cases Classical.em a with
      | inl ha =>
        cases Classical.em b with
        | inl hb => exact h2 (fun ha => hb)
        | inr hnb =>
          have hc : c := by
            cases h ha with
            | inl hb => contradiction
            | inr hc => exact hc
          exact Or.inr (fun ha => hc)
      | inr hna => exact h2 (fun ha => False.elim (hna ha))
  · intro h
    intro ha
    cases h with
    | inl h1 => exact Or.inl (h1 ha)
    | inr h2 => exact Or.inr (h2 ha)