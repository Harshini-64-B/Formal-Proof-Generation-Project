theorem length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ ∃ a : α, ∃ t : List α, a :: t = l ∧ t.length = n := by
  constructor
  · intro h
    cases l with
    | nil => contradiction
    | cons a t =>
      injection h with h'
      exact ⟨a, t, rfl, h'⟩
  · intro ⟨a, t, h1, h2⟩
    subst h1 h2
    rfl