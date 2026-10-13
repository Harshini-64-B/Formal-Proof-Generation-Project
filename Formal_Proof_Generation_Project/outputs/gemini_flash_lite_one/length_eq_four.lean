theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d: α, l = [a, b, c, d] := by
  constructor
  · intro h
    rcases l with | nil => contradiction | cons a l =>
    rcases l with | nil => contradiction | cons b l =>
    rcases l with | nil => contradiction | cons c l =>
    rcases l with | nil => contradiction | cons d l =>
    rcases l with | nil =>
      use a, b, c, d
      rfl
    | cons _ _ => contradiction
  · rintro ⟨a, b, c, d, rfl⟩
    rfl