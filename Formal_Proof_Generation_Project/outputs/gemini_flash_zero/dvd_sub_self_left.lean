import Mathlib.Data.Nat.Basic

theorem dvd_sub_self_left {n m : ℕ} : n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  constructor
  · intro h
    by_cases h1 : m = 0
    · left; exact h1
    · by_cases h2 : n ≤ m
      · right; exact h2
      · have h3 : 0 < n - m := by omega
        have h4 : n ≤ n - m := Nat.le_of_dvd h3 h
        omega
  · rintro (rfl | h)
    · simp
    · rw [Nat.sub_eq_zero_of_le h]
      exact dvd_zero n