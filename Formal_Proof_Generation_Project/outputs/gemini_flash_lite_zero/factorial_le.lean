theorem factorial_le {m n} (h : m ≤ n) : Nat.factorial m ≤ Nat.factorial n := by
  induction h with
  | refl => rfl
  | step h_le ih =>
    exact Nat.le_trans ih (Nat.le_mul_of_pos_right _ (Nat.factorial_pos _))