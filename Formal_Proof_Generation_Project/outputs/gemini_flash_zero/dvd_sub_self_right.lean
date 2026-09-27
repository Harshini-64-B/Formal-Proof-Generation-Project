import Mathlib.Data.Nat.Basic

theorem dvd_sub_self_right {n m : ℕ} : n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  rcases le_or_gt m n with h | h
  · simp [h]
  · simp [not_le.mpr h]
    constructor
    · intro h2
      have h3 := dvd_add h2 (dvd_refl n)
      rwa [Nat.sub_add_cancel (le_of_lt h)] at h3
    · intro h2
      exact Nat.dvd_sub (le_of_lt h) h2 (dvd_refl n)