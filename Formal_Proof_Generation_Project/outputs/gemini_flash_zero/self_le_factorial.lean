theorem self_le_factorial : ∀ n : ℕ, n ≤ Nat.factorial n
  | 0 => Nat.zero_le _
  | n + 1 => by
    have h : 1 ≤ Nat.factorial n := Nat.factorial_pos n
    have h2 : (n + 1) * 1 ≤ (n + 1) * Nat.factorial n := Nat.mul_le_mul_left (n + 1) h
    rw [Nat.mul_one] at h2
    exact h2