theorem one_lt_factorial : 1 < Nat.factorial n ↔ 1 < n := by
  constructor
  · intro h
    cases n with
    | zero => contradiction
    | succ m =>
      cases m with
      | zero => contradiction
      | succ k =>
        rw [Nat.factorial_succ, Nat.factorial_succ] at h
        -- m = succ k, so n = succ (succ k) >= 2 > 1
        exact Nat.succ_lt_succ (Nat.zero_lt_succ k)
  · intro h
    cases n with
    | zero => contradiction
    | succ m =>
      cases m with
      | zero => contradiction
      | succ k =>
        rw [Nat.factorial_succ, Nat.factorial_succ]
        have : 1 ≤ Nat.factorial (succ k) := Nat.factorial_pos k
        calc 1 < 1 + Nat.factorial (succ k) := Nat.lt_add_left _ _ _ this
        _ ≤ succ (succ k) * Nat.factorial (succ k) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)