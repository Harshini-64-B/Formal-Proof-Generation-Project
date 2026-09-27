import Mathlib.Data.Nat.Choose.Basic

-- You cannot choose k elements from n elements when k > n, so the binomial coefficient is 0.
theorem choose_eq_zero_iff {n k : ℕ} : Nat.choose n k = 0 ↔ n < k := by
  constructor
  · intro h
    contrapose! h
    exact Nat.choose_ne_zero_iff.mpr h
  · intro h
    exact Nat.choose_eq_zero_of_lt h
