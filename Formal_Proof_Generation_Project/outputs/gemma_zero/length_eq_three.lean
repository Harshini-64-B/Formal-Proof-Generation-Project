theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c : α, l = [a, b, c] := by
  constructor
  · intro h
    cases l
    · contradiction
    · intro a t
      cases t
      · contradiction
      · intro b t'
        cases t'
        · contradiction
        · intro c t''
          cases t''
          · exists a; exists b; exists c; rfl
          · contradiction
  · intro h
    cases h with
    | intro a b c eq => rw [eq]; simp