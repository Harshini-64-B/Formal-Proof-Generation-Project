theorem factorial_dvd_factorial {m n} (h : m ≤ n) : Nat.factorial m ∣ Nat.factorial n := by
  induction' h with n h ih
  · exact dvd_refl _
  · exact dvd_trans ih (Nat.dvd_mul_right (n.factorial) (n + 1))