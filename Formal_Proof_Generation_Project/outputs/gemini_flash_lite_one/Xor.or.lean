theorem Xor.or {a b : Prop} (h : Xor a b) : a ∨ b := by
  rcases h with ⟨hab, hnb⟩ | ⟨hab, hnb⟩
  · left
    exact hab
  · right
    exact hab