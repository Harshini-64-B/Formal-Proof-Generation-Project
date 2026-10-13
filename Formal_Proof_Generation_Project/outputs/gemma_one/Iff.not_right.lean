theorem Iff.not_right {a b : Prop} (h : ¬a ↔ b) : a ↔ ¬b := by
  constructor
  . intro ha hb
    exact h.mpr hb ha
  . intro hnb ha
    exact h.mp ha hnb