theorem length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ ∃ a : α, ∃ t : List α, a :: t = l ∧ t.length = n := by
  cases l with
  | nil =>
    simp only [List.length_nil, Nat.zero_eq_add_one, false_iff, not_exists]
    intro a t h
    exact h.symm ▸ nofun
  | cons a t =>
    simp only [List.length_cons, Nat.succ.injEq]
    constructor
    · intro h
      use a, t
      exact ⟨rfl, h⟩
    · rintro ⟨a', t', ⟨h1, h2⟩⟩
      injection h1 with h3 h4
      subst h4
      exact h2.symm