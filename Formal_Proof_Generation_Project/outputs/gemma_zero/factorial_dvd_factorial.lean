theorem factorial_dvd_factorial {m n} (h : m ≤ n) : Nat.factorial m ∣ Nat.factorial n := by
  rw [Nat.factorial_mul_factorial_range h]
  exact Nat.dvd_mul (Nat.factorial_pos m) _