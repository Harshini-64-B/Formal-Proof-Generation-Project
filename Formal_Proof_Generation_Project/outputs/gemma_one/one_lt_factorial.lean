theorem one_lt_factorial : 1 < Nat.factorial n ↔ 1 < n := by
  constructor
  · intro h
    match n with
    | 0 => contradiction
    | 1 => contradiction
    | m + 2 => exact Nat.lt_succ_of_le (by simp)
  · intro h
    cases n with
    | zero => contradiction
    | succ n' =>
      cases n' with
      | zero => contradiction
      | succ n'' =>
        have h_n_fact_ge_2 : Nat.factorial n ≥ 2 := by
          rw [Nat.factorial_succ]
          apply Nat.mul_le_mul_left
          · exact Nat.succ_le_of_le (by simp)
          · apply Nat.factorial_pos
          apply Nat.mul_le_mul_left
          · exact Nat.one_le_mul (by simp)
          · exact Nat.one_le_mul (by simp)
        exact Nat.lt_of_le_of_lt h_n_fact_ge_2 Nat.one_lt_two