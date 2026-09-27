theorem length_eq_four {l : List α} : l.length = 4 ↔ ∃ a b c d, l = [a, b, c, d] := by
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
            rw [List.length_cons, List.length_cons, List.length_cons, List.length_cons] at h
            simp at h
            cases w with
            | nil => exact ⟨a, b, c, d, rfl⟩
            | _ :: _ => contradiction
  · intro h
    obtain ⟨a, b, c, d, r⟩ := h
    rw [r]
    simp