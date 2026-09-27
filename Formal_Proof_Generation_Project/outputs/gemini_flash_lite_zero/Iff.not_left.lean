theorem Iff.not_left {a b : Prop} (h : a ↔ ¬b) : ¬a ↔ b := by
  constructor
  · intro ha
    by_contra hb
    exact ha (h.mp.mt hb)
  · intro hb ha
    exact (h.mp ha) hb