import Mathlib.Data.Nat.Factorial.Basic

theorem factorial_eq_one {n : ℕ} : Nat.factorial n = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    by_contra hc
    have hc : 2 ≤ n := by omega
    have h2 : 2 ≤ n.factorial := le_trans hc (Nat.self_le_factorial n)
    omega
  · intro h
    rcases n with _ | _ | n
    · rfl
    · rfl
    · omega