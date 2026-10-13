theorem not_and_or {a b : Prop} : ¬(a ∧ b) ↔ ¬a ∨ ¬b := by
  constructor
  · intro h
    cases Classical.em a with
    | inl a_true =>
      cases Classical.em b with
      | inl b_true =>
        exact h (And.intro a_true b_true)
      | inr b_false =>
        right; exact b_false
    | inr a_false =>
      left; exact a_false
  · intro h
    intro hab
    cases h with
    | inl ha_not => exact ha_not (And.left hab)
    | inr hb_not => exact hb_not (And.right hab)