import Mathlib.Data.List.Basic

theorem length_eq_succ_iff {n} {l : List α} : l.length = n + 1 ↔ ∃ a : α, ∃ t : List α, a :: t = l ∧ t.length = n := by
  sorry
