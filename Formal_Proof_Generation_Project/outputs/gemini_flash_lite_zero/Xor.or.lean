theorem Xor.or {a b : Prop} (h : Xor a b) : a ∨ b := by
  rcases h with ⟨hab, _⟩ | ⟨_, hab⟩
  · exact Or.inl hab.1
  · exact Or.inr hab.2