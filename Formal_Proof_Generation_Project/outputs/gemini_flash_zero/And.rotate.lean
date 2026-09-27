theorem And.rotate {a b c : Prop} : a ∧ b ∧ c → b ∧ c ∧ a := by
  intro h
  exact ⟨h.right.left, h.right.right, h.left⟩