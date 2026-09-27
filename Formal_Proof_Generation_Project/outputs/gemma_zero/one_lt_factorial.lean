theorem one_lt_factorial (n : Nat) : 1 < Nat.factorial n ↔ 1 < n := by
  constructor
  · intro h
    cases n with
    | zero => contradiction
    | succ n =>
      cases n with
      | zero => contradiction
      | succ n =>
        have h_fact : Nat.factorial (n + 2) ≥ 2 := by
          apply Nat.le_trans (Nat.factorial_ge_self (n + 2))
          simp
        exact Nat.lt_of_le_of_lt h_fact (by simp)
  · intro h
    cases n with
    | zero =>
      simp [Nat.factorial_zero] at h
      contradiction
    | succ n =>
      cases n with
      | zero =>
        simp [Nat.factorial_one] at h
        contradiction
      | succ n =>
        simp at h
        exact h