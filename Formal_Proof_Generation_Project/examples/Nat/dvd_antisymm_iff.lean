import Mathlib.Data.Nat.Basic

-- Two natural numbers dividing each other are equal.
theorem dvd_antisymm_iff {m n : ℕ} : m = n ↔ m ∣ n ∧ n ∣ m := by
  constructor
  . intro h
    simp_all
  . intro h
    rcases h with ⟨h1, h2⟩
    exact Nat.dvd_antisymm h1 h2
