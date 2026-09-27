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
      · exact Nat.add_one_cancel h
  · intro ⟨a, t, h_eq, h_len⟩
    rw [h_eq, h_len, List.length_cons]
    simp