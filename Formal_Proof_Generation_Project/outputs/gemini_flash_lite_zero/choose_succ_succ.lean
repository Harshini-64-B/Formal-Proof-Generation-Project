theorem nat_choose_two_mul (n : ) : n.choose 2 * 2 = n * (n - 1) := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      have h1 : (Nat.succ (Nat.succ n)).choose 2 = (Nat.succ n + 1) * (Nat.succ n) / 2 := rfl
      rw [h1]
      have h2 : 2 ≤ (Nat.succ n + 1) * (Nat.succ n) := by
        exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _))
      rw [Nat.div_mul_cancel (by omega)]
      ring