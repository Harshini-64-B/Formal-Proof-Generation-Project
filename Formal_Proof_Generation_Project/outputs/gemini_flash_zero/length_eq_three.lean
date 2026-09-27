theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c : α, l = [a, b, c] := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a l =>
      cases l with
      | nil => contradiction
      | cons b l =>
        cases l with
        | nil => contradiction
        | cons c l =>
          cases l with
          | nil => exact ⟨a, b, c, rfl⟩
          | cons d tl => contradiction
  · rintro ⟨a, b, c, rfl⟩
    rfl