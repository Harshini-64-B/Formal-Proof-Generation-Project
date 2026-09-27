theorem dvd_left_injective : Function.Injective fun (x1 x2 : ℕ) => x1 ∣ x2 := by
  intro x1 x2 h
  have h1 : x2 ∣ x1 := by rw [← h, Nat.dvd_self x1]
  have h2 : x1 ∣ x2 := by rw [← h, Nat.dvd_self x2]
  exact Nat.dvd_antisymm h2 h1