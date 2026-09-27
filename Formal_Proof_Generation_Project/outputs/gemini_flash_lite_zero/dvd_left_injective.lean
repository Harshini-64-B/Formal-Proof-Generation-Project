theorem dvd_left_injective: Function.Injective fun (x1 x2 : ℕ) => x1 ∣ x2 := by
  intro x1 x2 h
  have h1 : x1 ∣ x1 := dvd_rfl
  have h2 : x1 ∣ x2 := by rw [h]; exact dvd_rfl
  have h3 : x2 ∣ x2 := dvd_rfl
  have h4 : x2 ∣ x1 := by rw [h] at h1; exact h1
  exact Nat.dvd_antisymm h2 h4