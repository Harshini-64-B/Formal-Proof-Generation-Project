theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [Nat.sub_succ_cancel]
  have h : n * (n - 1) + 2 * n = n * (n + 1) := by ring
  rw [← Nat.div_add_mul_div_eq_div_add]
  rw [← h]
  rw [← Nat.mul_comm n (n + 1)]
  rfl