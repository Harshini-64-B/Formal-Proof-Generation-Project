theorem mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) : a * b ≤ a ^ b := by
  induction' b with b ih
  · simp
  · by_cases hb : b = 0
    · subst hb
      simp
    · have ha2 : 2 ≤ a := by
        rcases a with _ | _ | a
        · contradiction
        · contradiction
        · exact Nat.succ_le_succ (Nat.zero_le _)
      have h1 : a * b ≤ a ^ b := ih
      have h2 : a ≤ a ^ b := by
        calc a = a ^ 1 := by rw [pow_one]
        _ ≤ a ^ b := Nat.pow_le_pow_right ha2 (Nat.pos_of_ne_zero hb)
      calc a * (b + 1) = a * b + a := by ring
      _ ≤ a ^ b + a ^ b := add_le_add h1 h2
      _ = 2 * a ^ b := by ring
      _ ≤ a * a ^ b := Nat.mul_le_mul_right (a ^ b) ha2
      _ = a ^ (b + 1) := by rw [pow_succ]