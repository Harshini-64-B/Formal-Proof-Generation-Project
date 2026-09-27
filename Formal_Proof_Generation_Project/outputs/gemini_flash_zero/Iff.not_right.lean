theorem Iff.not_right {a b : Prop} (h : ¬a ↔ b) : a ↔ ¬b := by
  constructor
  · intro ha hb
    exact (h.mp hb) ha
  · intro hnb
    by_contra ha
    exact hnb (h.mp ha)