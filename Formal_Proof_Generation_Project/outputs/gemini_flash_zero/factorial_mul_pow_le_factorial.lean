import Mathlib.Data.Nat.Factorial.Basic

theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, Nat.factorial m * (m + 1) ^ n ≤ Nat.factorial (m + n) := by
  intro m n
  induction' n with n ih
  · simp
  · rw [pow_succ, ← mul_assoc]
    have h1 : Nat.factorial m * (m + 1) ^ n * (m + 1) ≤ Nat.factorial (m + n) * (m + 1) :=
      Nat.mul_le_mul_right (m + 1) ih
    apply h1.trans
    rw [Nat.add_assoc, Nat.factorial_succ, mul_comm (m + n + 1)]
    apply Nat.mul_le_mul_left
    omega