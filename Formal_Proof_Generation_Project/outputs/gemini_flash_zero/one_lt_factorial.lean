import Mathlib.Data.Nat.Factorial.Basic

theorem one_lt_factorial : 1 < Nat.factorial n ↔ 1 < n := by
  match n with
  | 0 => simp
  | 1 => simp
  | Nat.succ (Nat.succ n) =>
    have := Nat.self_le_factorial (n + 2)
    omega