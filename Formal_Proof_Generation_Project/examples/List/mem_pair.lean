import Mathlib.Data.List.Basic

theorem mem_pair {a b c : α} : a ∈ [b, c] ↔ a = b ∨ a = c := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h
