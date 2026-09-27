theorem factorial_eq_one : ∀ n : ℕ, Nat.factorial n = 1 ↔ n ≤ 1 := by
  intro n
  constructor
  · intro h
    cases n with
    | zero => rfl
    | succ n1 =>
      cases n1 with
      | zero => rfl
      | succ n2 =>
        have : Nat.factorial (n2 + 2) > 1 := by
          rw [Nat.factorial_succ, Nat.factorial_succ]
          simp
        contradiction
  · intro h
    cases n with
    | zero => rfl
    | succ n1 =>
      cases n1 with
      | zero => rfl
      | succ _ => contradiction