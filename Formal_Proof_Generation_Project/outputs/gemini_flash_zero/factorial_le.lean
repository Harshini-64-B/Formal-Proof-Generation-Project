theorem factorial_le {m n} (h : m ≤ n) : Nat.factorial m ≤ Nat.factorial n := by
  induction h with
  | refl => exact Nat.le_refl _
  | step _ ih =>
    apply Nat.le_trans ih
    exact Nat.le_mul_of_pos_left (Nat.factorial _) (Nat.succ_pos _)