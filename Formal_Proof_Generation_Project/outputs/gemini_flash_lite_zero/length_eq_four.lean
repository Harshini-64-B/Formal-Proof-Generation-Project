theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d: α, l = [a, b, c, d] := by
  constructor
  · rintro (_ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨_, _⟩⟩⟩⟩⟩)
    exact ⟨a, b, c, d, rfl⟩
  · rintro ⟨a, b, c, d, rfl⟩
    rfl