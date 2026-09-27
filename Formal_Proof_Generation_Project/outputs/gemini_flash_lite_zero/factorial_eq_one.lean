theorem factorial_eq_one : Nat.factorial n = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    match n with
    | 0 => exact Nat.zero_le 1
    | 1 => exact Nat.le_refl 1
    | m + 2 =>
      have : Nat.factorial (m + 2) = (m + 2) * Nat.factorial (m + 1) := rfl
      have : Nat.factorial (m + 1) ≥ 1 := Nat.factorial_pos (m + 1)
      have : (m + 2) * Nat.factorial (m + 1) ≥ 2 * 1 := by
        apply Nat.mul_le_mul <;> linarith
      rw [this] at h
      contradiction
  · intro h
    interval_cases n <;> rfl