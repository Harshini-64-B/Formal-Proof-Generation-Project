import Mathlib.Data.Nat.Choose.Basic

theorem choose_ne_zero {n k : ℕ} (h : k ≤ n) : n.choose k ≠ 0 := by
  exact (Nat.choose_pos h).ne'