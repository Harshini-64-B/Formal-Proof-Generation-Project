theorem xor_not_right {a b : Prop} : Xor a ¬b ↔ (a ↔ b) := by
  rw [Xor]
  constructor
  · intro h
    let ⟨h1, h2⟩ := h
    constructor
    · intro ha
      rw [h2] at ha
      exact ha.elim
    · intro hb
      rw [h2] at hb
      exact hb.elim
  · intro h
    constructor
    · intro ha
      exact Or.elim (Or.inl ha) (Or.inr (fun hb => by rw [h] at hb; exact hb.elim))
    · intro hb
      exact Or.elim (Or.inr hb) (Or.inl (fun ha => by rw [h] at ha; exact ha.elim))