theorem Iff.not {a b : Prop} (h : a ↔ b) : ¬a ↔ ¬b := by
  constructor
  · intro ha hb
    apply ha
    exact h.mpr hb
  · intro hb ha
    apply hb
    exact h.mp ha