theorem length_eq_two {l : List α} : l.length = 2 ↔ ∃ a b : α, l = [a, b] := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a t =>
      cases t with
      | nil => contradiction
      | cons b u =>
        cases u with
        | nil => exact ⟨a, b, rfl⟩
        | cons _ _ => contradiction
  · intro h
    cases h with
    | intro a b eq =>
      simp [eq]