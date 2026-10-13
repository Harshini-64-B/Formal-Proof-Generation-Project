theorem Iff.not_right {a b : Prop} (h : ¬a ↔ b) : a ↔ ¬b := by
  constructor
  · intro ha hb
    have hna : ¬a := ha
    have hb' : b := h.mp hna
    exact hb hb'
  · intro hnb
    by_contra ha
    have hna : ¬a := ha
    have hb : b := h.mp hna
    exact hnb hb