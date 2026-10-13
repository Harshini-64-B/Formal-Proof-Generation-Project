theorem dvd_left_injective: Function.Injective fun (x1 x2 : ℕ) => x1 ∣ x2 := by
  intro x1 y1 h
  have h1 : y1 ∣ x1 := h x1 |>.mpr (Nat.dvd_self x1)
  have h2 : x1 ∣ y1 := h y1 |>.mp (Nat.dvd_self y1)
  exact Nat.dvd_antisymm h2 h1