theorem Iff.not_left {a b : Prop} (h : a ↔ ¬b) : ¬a ↔ b := by
  constructor
  · intro hna
    by_contra hnb
    exact hna (h.mpr hnb)
  · intro hb ha
    exact (h.mp ha) hb