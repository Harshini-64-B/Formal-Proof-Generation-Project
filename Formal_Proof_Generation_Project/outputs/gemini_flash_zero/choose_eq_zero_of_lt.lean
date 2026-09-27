theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → Nat.choose n k = 0
  | _, 0, h => by cases h
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    have h1 : n < k := Nat.lt_of_succ_lt_succ h
    have h2 : n < k + 1 := Nat.lt_succ_of_lt h1
    show Nat.choose n k + Nat.choose n (k + 1) = 0
    rw [choose_eq_zero_of_lt h1, choose_eq_zero_of_lt h2]