theorem mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) : a * b ≤ a ^ b := by
  cases a with
  | zero => norm_num
  | succ a_1 =>
    cases a_1 with
    | zero => contradiction
    | succ _ =>
      induction b with
      | zero => norm_num
      | succ b ih =>
        have h_ih : a * b ≤ a ^ b := ih
        have h_pow : a ^ (b + 1) = a ^ b * a := Nat.pow_succ a b
        rw [h_pow]
        if hb : b = 0 then
          norm_num
        else
          apply Nat.mul_le_of_le_of_le
          · apply Nat.mul_le_of_le
            exact Nat.mul_left_comm a b
            exact h_ih
          · have ha2 : a ≥ 2 := by
              cases a with
              | zero => contradiction
              | succ a_3 =>
                cases a_3 with
                | zero => contradiction
                | succ _ => norm_num
          have hb1 : b ≥ 1 := by linarith
          have : a * (b + 1) ≤ a * a * b := by linarith
          exact this