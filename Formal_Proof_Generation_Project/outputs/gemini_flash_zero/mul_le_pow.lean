theorem mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) : a * b ≤ a ^ b := by
  rcases a with _ | a
  · cases b <;> simp
  · rcases a with _ | a
    · contradiction
    · have ha2 : 2 ≤ a + 2 := by omega
      induction b with
      | zero => simp
      | succ b ih =>
        rcases b with _ | b
        · simp
        · have h_pow : a + 2 ≤ (a + 2) ^ (b + 1) := by
            induction b with
            | zero => simp
            | succ b ih2 =>
              have h_le : (a + 2) ^ (b + 1) ≤ (a + 2) ^ (b + 2) := by
                have h_step : (a + 2) ^ (b + 2) = (a + 2) ^ (b + 1) * (a + 2) := by ring
                rw [h_step]
                have := Nat.mul_le_mul_left ((a + 2) ^ (b + 1)) (show 1 ≤ a + 2 by omega)
                simpa using this
              omega
          have h1 : (a + 2) * (b + 2) = (a + 2) * (b + 1) + (a + 2) := by ring
          have h2 : (a + 2) ^ (b + 2) = (a + 2) ^ (b + 1) * (a + 2) := by ring
          rw [h1, h2]
          have h5 : (a + 2) ^ (b + 1) * 2 ≤ (a + 2) ^ (b + 1) * (a + 2) := Nat.mul_le_mul_left _ ha2
          omega