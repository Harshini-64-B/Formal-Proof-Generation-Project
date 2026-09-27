theorem choose_succ_self (n : ℕ) : Nat.choose n (Nat.succ n) = 0 :=
  Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)