theorem nat_choose_two_mul (n : ) : (2 * n).choose n = (2 * n).choose (n + 1) := by
  have h : n + 1 + n = 2 * n := by omega
  exact (Nat.choose_symm h).symm