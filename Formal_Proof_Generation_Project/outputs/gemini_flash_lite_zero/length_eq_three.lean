theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c : α, l = [a, b, c] := by
  constructor
  · rintro ⟨a, b, c, rfl⟩ | ⟨a, ⟨b, ⟨c, rfl⟩⟩⟩
    · contradiction
    · rintro ⟨d, rfl⟩ | ⟨d, ⟨e, rfl⟩⟩
      · contradiction
      · rintro ⟨f, rfl⟩ | h
        · use a, b, c
        · contradiction
  · rintro ⟨a, b, c, rfl⟩
    rfl