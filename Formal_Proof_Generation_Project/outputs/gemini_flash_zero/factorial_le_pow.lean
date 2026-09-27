import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

theorem factorial_le_pow : ∀ n, Nat.factorial n ≤ n ^ n
  | 0 => by simp
  | n + 1 => by
    rw [Nat.factorial_succ, pow_succ, mul_comm ((n + 1) ^ n)]
    gcongr
    refine le_trans (factorial_le_pow n) ?_
    gcongr
    omega