theorem factorial_dvd_factorial {m n} (h : m ≤ n) : Nat.factorial m ∣ Nat.factorial n := by
  induction n with
  | zero =>
    simp at h
    simp
  | succ n ih =>
    cases' (Nat.le_or_gt h) with h_le h_gt
    · have h_ih : Nat.factorial m ∣ Nat.factorial n := ih h_le
      have h_succ : Nat.factorial n ∣ Nat.factorial (n + 1) := by
        rw [Nat.factorial_succ]
      exact Nat.dvd_trans h_ih h_succ
    · have h_m : m = n + 1 := by
        have h_ge : n + 1 ≤ m := Nat.succ_le_of_lt h_gt
        exact Nat.le_antisymm h h_ge
      rw [h_m]
      simp