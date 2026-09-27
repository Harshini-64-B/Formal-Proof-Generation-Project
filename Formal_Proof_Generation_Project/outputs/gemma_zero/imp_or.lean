theorem imp_or {a b c : Prop} : a → b ∨ c ↔ (a → b) ∨ (a → c) := by
  constructor
  · intro h
    by classical
    cases em a with
    | inl ha =>
      cases h ha with
      | inl hb => left; intro _; exact hb
      | inr hc => right; intro _; exact hc
    | inr hna => left; intro a; exact hna a
  · intro h
    cases h with
    | inl hab => intro a; left; exact hab a
    | inr hac => intro a; right; exact hac a