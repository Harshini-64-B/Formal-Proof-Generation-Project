theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b : α, l = [a, b] := by
  constructor
  · rintro (_ | ⟨a, _ | ⟨b, _ | l⟩⟩) hl
    · contradiction
    · contradiction
    · exact ⟨a, b, rfl⟩
    · contradiction
  · rintro ⟨a, b, rfl⟩
    rfl