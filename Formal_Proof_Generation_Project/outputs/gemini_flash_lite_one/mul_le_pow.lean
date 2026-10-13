theorem mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) : a * b ≤ a ^ b := by
  rcases b with _ | b
  · simp
  · rcases b with _ | b
    · simp
    · have ha2 : 2 ≤ a := by
        rcases a with _ | _ | a
        · contradiction
        · contradiction
        · omega
      have h_pow : 2 * (b + 2) ≤ 2 ^ (b + 2) := by
        induction' b with k ih
        · decide
        · have : 2 ^ (k + 1 + 2) = 2 * 2 ^ (k + 2) := by ring
          rw [this]
          omega
      have ha_le : 2 ^ (b + 2) ≤ a ^ (b + 2) := Nat.pow_le_pow_left ha2 (b + 2)
      have : 2 * (b + 2) ≤ a ^ (b + 2) := le_trans h_pow ha_le
      have : a * (b + 2) ≤ 2 * (b + 2) := by
        apply Nat.mul_le_mul_right
        omega
      exact le_trans this (le_trans h_pow ha_le)