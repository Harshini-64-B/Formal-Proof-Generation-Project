theorem ex_1_3_7 (P Q R : Prop) : (P ∧ Q → R) → (P → Q → R) := by
  intro h p q
  apply h
  exact ⟨p, q⟩