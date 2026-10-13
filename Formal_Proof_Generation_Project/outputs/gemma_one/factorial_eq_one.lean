theorem factorial_eq_one (n : ℕ) : Nat.factorial n = 1 ↔ n ≤ 1 := by
  constructor
  · intro h
    exact (Nat.factorial_ge n).trans h
  · intro h
    cases n with
    | zero => rfl
    | succ n' =>
      cases n' with
      | zero => rfl
      | succ _ => contradiction