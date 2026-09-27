theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  have h1 : n + 1 - 1 = n := by omega
  rw [h1]
  have h2 : (n + 1) * n = n * (n - 1) + 2 * n := by
    rcases n with _ | k
    · rfl
    · ring
  rw [h2, Nat.add_div_right _ (by norm_num)]
  rw [Nat.mul_div_cancel_left _ (by norm_num)]