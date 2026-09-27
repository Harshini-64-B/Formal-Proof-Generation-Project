theorem Iff.not_right {a b : Prop} (h : ¬a ↔ b) : a ↔ ¬b := by
  constructor
  · intro ha hb
    have : ¬a := fun hA => hA ha
    have : b := h.mp this
    contradiction
  · intro hnb
    by_contra ha
    have : b := h.mp ha
    contradiction