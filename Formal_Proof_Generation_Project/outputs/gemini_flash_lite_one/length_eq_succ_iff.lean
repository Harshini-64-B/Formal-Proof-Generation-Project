theorem length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ ∃ a : α, ∃ t : List α, a :: t = l ∧ t.length = n := by
  constructor
  · intro h
    cases l with
    | nil =>
      rw [List.length_nil] at h
      contradiction
    | cons a t =>
      use a, t
      refine ⟨rfl, ?_⟩
      dsimp [List.length] at h
      exact Nat.succ.inj h
  · rintro ⟨a, t, rfl, ht⟩
    dsimp [List.length]
    rw [ht]