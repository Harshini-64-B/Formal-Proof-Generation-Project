theorem choose_symm_of_eq {n k m : ℕ} (h : k + m = n) : Nat.choose n k = Nat.choose n m := by
  have h1 : n - k = m := by omega
  have h2 : n - m = k := by omega
  rw [← h1, ← h2]
  exact Nat.choose_symm (by omega)