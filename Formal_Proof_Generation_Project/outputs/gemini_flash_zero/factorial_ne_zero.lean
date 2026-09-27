theorem factorial_ne_zero (n : ℕ) : Nat.factorial n ≠ 0 := by
  induction n with
  | zero => exact Nat.succ_ne_zero 0
  | succ n ih =>
    intro h
    cases Nat.mul_eq_zero.mp h with
    | inl h1 => exact Nat.succ_ne_zero n h1
    | inr h2 => exact ih h2