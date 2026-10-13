theorem pow_right_injective {a : ℕ} (ha : 2 ≤ a) : Function.Injective fun (x : ℕ) => a ^ x := by
  intro x y h
  induction x with
  | zero =>
    simp at h
    have hy_zero : y = 0 := by
      induction y with
      | zero => rfl
      | succ y' =>
        simp at h
        have h_pow_ge_2 : 2 ≤ a ^ (y' + 1) := Nat.pow_ge_two ha (Nat.one_le_succ y')
        exact (Nat.ne_one_of_ge_two h_pow_ge_2).mp h
    exact hy_zero
  | succ x' =>
    cases y with
    | zero =>
      simp at h
      have h_pow_ge_2 : 2 ≤ a ^ (x' + 1) := Nat.pow_ge_two ha (Nat.one_le_succ x')
      exact (Nat.ne_one_of_ge_two h_pow_ge_2).mp h
    | succ y' =>
      have ha_ne_zero : a ≠ 0 := Nat.pos_of_ge_two ha
      have h_eq : a ^ x' = a ^ y' := by
        apply Nat.mul_cancel ha_ne_zero
        exact h
      exact ih y' h_eq