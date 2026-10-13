theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d: α, l = [a, b, c, d] := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a t =>
      cases t with
      | nil => contradiction
      | cons b u =>
        cases u with
        | nil => contradiction
        | cons c v =>
          cases v with
          | nil => contradiction
          | cons d w =>
            cases w with
            | nil => use a, b, c, d; rfl
            | cons _ _ => contradiction
  · intro ⟨a, b, c, d, h⟩
    rw [h]
    simp