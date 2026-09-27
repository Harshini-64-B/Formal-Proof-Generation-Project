import Mathlib.Data.Nat.Factorial.Basic

-- For any natural number n, if n is at least 3, then n is less than its factorial n!.
theorem lt_factorial_self {n : ℕ} (hi : 3 ≤ n) : n < Nat.factorial n := by
  have : 0 < n := by lia
  have hn : 1 < Nat.pred n := Nat.le_pred_of_lt (Nat.succ_le_iff.mp hi)
  rw [← Nat.succ_pred_eq_of_pos ‹0 < n›, Nat.factorial_succ]
  exact (Nat.lt_mul_iff_one_lt_right (Nat.pred n).succ_pos).2 ((Nat.lt_of_lt_of_le hn (Nat.self_le_factorial _)))
