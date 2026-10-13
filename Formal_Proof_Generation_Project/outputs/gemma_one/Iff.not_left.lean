theorem Iff.not_left {a b : Prop} (h : a ↔ ¬b) : ¬a ↔ b := by
  constructor
  · intro h_na
    by_contra h_nb
    exact h_na (h.mpr h_nb)
  · intro h_b
    intro h_a
    exact h.mp h_a h_b