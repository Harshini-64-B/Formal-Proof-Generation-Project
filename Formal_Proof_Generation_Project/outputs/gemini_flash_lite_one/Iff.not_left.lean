theorem Iff.not_left {a b : Prop} (h : a ↔ ¬b) : ¬a ↔ b := by
  constructor
  · intro ha
    by_contra hb
    apply ha
    exact h.mp.mpr hb
  · intro hb ha
    apply h.mpr hb
    exact ha