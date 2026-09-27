theorem Iff.not {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b := by
  constructor
  · intro h_na
    intro h_b
    exact h_na (h.mpr h_b)
  · intro h_nb
    intro h_a
    exact h_nb (h.mp h_a)