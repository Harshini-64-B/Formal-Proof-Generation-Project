theorem length_eq_three {l : List α} : l.length = 3 ↔ ∃ a b c : α, l = [a, b, c] := by
  constructor
  · intro h
    rcases l with | nil => contradiction | cons a l =>
    rcases l with | nil => contradiction | cons b l =>
    rcases l with | nil => contradiction | cons c l =>
    rcases l with | nil =>
      use a, b, c
      rfl
    | cons d l => contradiction
  · rintro ⟨a, b, c, rfl⟩
    rfl