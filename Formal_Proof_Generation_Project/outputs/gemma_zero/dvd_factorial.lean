theorem dvd_factorial {m n : ℕ} (hm : 0 < m) (hn : m ≤ n) : m ∣ Nat.factorial n := by
  induction n with
  | zero =>
    simp at hm
    exact hm.not
  | succ n ih =>
    rw [Nat.factorial_succ]
    exact Nat.dvd_mul_right (ih hm hn) (n + 1)