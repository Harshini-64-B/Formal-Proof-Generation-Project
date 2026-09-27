theorem Iff.not {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b := by
  constructor
  · intro hna hb
    exact hna (h.mpr hb)
  · intro hnb ha
    exact hnb (h.mp ha)