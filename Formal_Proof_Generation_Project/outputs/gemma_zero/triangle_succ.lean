theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [Nat.div_add_left]
  have h : (n + 1) * (n + 1 - 1) = n * (n - 1) + 2 * n := by omega
  rw [h]
  rfl