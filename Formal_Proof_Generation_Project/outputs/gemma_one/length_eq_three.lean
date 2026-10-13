theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c : α, l = [a, b, c] := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a xs =>
      cases xs with
      | nil => contradiction
      | cons b ys =>
        cases ys with
        | nil => contradiction
        | cons c zs =>
          cases zs with
          | nil => exact ⟨a, b, c, rfl⟩
          | cons _ _ => contradiction
  · intro h
    rcases h with ⟨a, b, c, rfl⟩
    simp