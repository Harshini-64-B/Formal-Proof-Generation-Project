import Mathlib.Data.Nat.Factorial.Basic

theorem factorial_dvd_factorial {m n} (h : m ≤ n) : Nat.factorial m ∣ Nat.factorial n := by
  induction h with
  | refl => rfl
  | step _ ih => exact dvd_mul_of_dvd_right ih _