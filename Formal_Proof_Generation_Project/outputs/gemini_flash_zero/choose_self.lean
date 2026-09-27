theorem choose_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → Nat.choose n k = 0
  | 0, 0, h => (Nat.not_lt_zero 0 h).elim
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => (Nat.not_lt_zero _ h).elim
  | n + 1, k + 1, h => by
    have h1 : n < k := Nat.lt_of_succ_lt_succ h
    have h2 : n < k + 1 := Nat.lt_trans h1 (Nat.lt_succ_self k)
    change Nat.choose n k + Nat.choose n (k + 1) = 0
    rw [choose_eq_zero_of_lt h1, choose_eq_zero_of_lt h2]

theorem choose_self (n : ℕ) : Nat.choose n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Nat.choose n n + Nat.choose n (n + 1) = 1
    have h : n < n + 1 := Nat.lt_succ_self n
    rw [ih, choose_eq_zero_of_lt h]
