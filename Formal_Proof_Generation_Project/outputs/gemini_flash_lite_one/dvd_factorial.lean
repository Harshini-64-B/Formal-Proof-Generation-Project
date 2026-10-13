theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ Nat.factorial n := by
  intro m n hm hmn
  exact Nat.dvd_factorial hm hmn