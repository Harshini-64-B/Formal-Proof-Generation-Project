theorem length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ ∃ a : α, ∃ t : List α, a :: t = l ∧ t.length = n := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a t =>
      exists a
      exists t
      constructor
      · rfl
      · rw [List.length_cons] at h
        exact Nat.succ_eq_succ_iff.mp h
  · intro h
    let ⟨a, t, h_eq, ht⟩ := h
    rw [h_eq, List.length_cons, ht]