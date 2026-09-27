theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ Nat.factorial n := by
  intro m n hm h
  induction' h with k hk ih
  · exact dvd_refl _
  · rw [Nat.factorial_succ]
    exact dvd_mul_of_dvd_right ih (k.succ)