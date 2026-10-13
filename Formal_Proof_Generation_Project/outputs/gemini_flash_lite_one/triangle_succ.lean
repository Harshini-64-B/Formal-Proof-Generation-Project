theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  have h1 : n + 1 - 1 = n := by omega
  rw [h1]
  have h2 : (n + 1) * n = n * (n - 1) + 2 * n := by
    rcases n with _ | n'
    · rfl
    · push_cast
      ring
  rw [h2]
  rw [Nat.add_mul_div_right _ _ (by omega : 0 < 2)]
  omega