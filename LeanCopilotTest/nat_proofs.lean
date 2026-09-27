import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import LeanCopilot

-- 1. The successor function on natural numbers is injective, i.e., If two natural numbers have the same successor, then the two numbers themselves must be equal.
-- theorem succ_injective {n m : Nat} : Nat.succ n = Nat.succ m → n = m := by
--   intro h
--   simp at h
--   exact h
theorem succ_injective : Function.Injective Nat.succ := by
  unfold Function.Injective
  intro m n h
  repeat rw[Nat.succ_eq_add_one] at h
  exact Nat.add_right_cancel h

-- 2. For natural-number division, dividing a number successively by b and then by c gives the same result as dividing it successively by c and then by b, i.e., commutativity of the divisors when performing successive division.
theorem div_right_comm (a b c : Nat) : a / b / c = a / c / b := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.div_div_eq_div_mul]

-- 3. If n ≠ 0 and a^n = b^n, then a=b.
theorem pow_left_injective {n : Nat} (hn : n ≠ 0) : Function.Injective fun (a : Nat) => a ^ n := by
  simp [Function.Injective, le_antisymm_iff, Nat.pow_le_pow_iff_left hn]

-- 4. If a≥2 and a^x = a^y, then x=y.
theorem pow_right_injective {a : ℕ} (ha : 2 ≤ a) : Function.Injective fun (x : ℕ) => a ^ x := by
  simp [Function.Injective, le_antisymm_iff, Nat.pow_le_pow_iff_right ha]

-- 5. If x and a are nonzero natural numbers, then x^(a−1) is equal to x^a divided by x.
theorem pow_sub_one {x a : ℕ} (hx : x ≠ 0) (ha : a ≠ 0) : x ^ (a - 1) = x ^ a / x := by
  rw [← Nat.pow_div (Nat.one_le_iff_ne_zero.mpr ha) (Nat.pos_iff_ne_zero.mpr hx), Nat.pow_one]

-- 6. If n divides n−m, then either m=0 or n≤m, and vice versa.
theorem dvd_sub_self_left {n m : ℕ} : n ∣ n - m ↔ m = 0 ∨ n ≤ m := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 7. If n divides m−n if and only if either n divides m or m≤n.
theorem dvd_sub_self_right {n m : ℕ} : n ∣ m - n ↔ n ∣ m ∨ m ≤ n := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 8. If two natural numbers divide exactly the same natural numbers, then the two numbers are equal.
theorem dvd_left_injective: Function.Injective fun (x1 x2 : ℕ) => x1 ∣ x2 := by
  unfold Function.Injective
  intro x1 x2 h
  simp at h
  apply Nat.dvd_right_iff_eq.mp fun a => iff_of_eq (congr_fun h a)

-- 9. If a ≠ 1, then for any natural number b, a×b ≤ a^b.
theorem mul_le_pow {a : ℕ} (ha : a ≠ 1) (b : ℕ) : a * b ≤ a ^ b := by
  cases b with
  | zero =>
        rw[Nat.mul_zero, Nat.pow_zero]
        exact Nat.zero_le _
  | succ t =>
          obtain rfl | ha0 : a = 0 ∨ a > 0 := a.eq_zero_or_pos
          · rw [Nat.zero_mul];
            exact Nat.zero_le _
          · have ha1 : a > 1 := Nat.lt_of_le_of_ne ha0 ha.symm
            rw [Nat.pow_succ'];
            exact Nat.mul_le_mul_left a (Nat.lt_pow_self ha1)

-- 10. For any natural number n, the binomial coefficient “n choose 0” is equal to 1.
theorem choose_zero_right (n : ℕ) : n.choose 0 = 1 := by
  unfold Nat.choose
  rfl

-- 11. For any natural number k, the binomial coefficient “0 choose k+1” is equal to 0.
theorem choose_zero_succ (k : ℕ) : Nat.choose 0 (Nat.succ k) = 0 := by
  unfold Nat.choose
  rfl

-- 12. For any natural numbers n and k, choosing k+1 objects from n+1 objects is equal to the number of ways to choose k objects from n objects plus the number of ways to choose k+1 objects from n objects.
theorem choose_succ_succ (n k : ℕ) : Nat.choose (Nat.succ n) (Nat.succ k) = Nat.choose n k + Nat.choose n (Nat.succ k) := by
  rfl

-- 13. For any natural numbers n and k with k>0, choosing k objects from n+1 objects is equal to the number of ways to choose k−1 objects from n objects plus the number of ways to choose k objects from n objects.
theorem choose_succ_left (n k : ℕ) (hk : 0 < k) : Nat.choose (n + 1) k = Nat.choose n (k - 1) + Nat.choose n k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rfl

-- 14. For any natural numbers n and k with n>0 and k>0, choosing k objects from n objects is equal to the number of ways to choose k−1 objects from n−1 objects plus the number of ways to choose k objects from n−1 objects.
theorem choose_eq_choose_pred_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) : Nat.choose n k = Nat.choose (n - 1) (k - 1) + Nat.choose (n - 1) k := by
  obtain ⟨l, rfl⟩ : ∃ l, k = l + 1 := Nat.exists_eq_add_of_le' hk
  rw [Nat.choose_succ_right _ _ hn, Nat.add_one_sub_one]

-- 15. If n<k, then the binomial coefficient of n choose k is equal to 0, i.e., we cannot choose more than n objects from a set of n objects, so the number of ways is 0.
theorem choose_eq_zero_of_lt : ∀ {n k}, n < k → Nat.choose n k = 0 := by
  intro n k h
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => exact (Nat.lt_irrefl 0 h).elim
      | succ k => rw[Nat.choose_zero_succ]
  | succ n ih =>
      cases k with
      | zero => exact (Nat.not_lt_zero _ h).elim
      | succ k => simp at h
                  rw [Nat.choose_succ_succ]
                  rw [ih h, ih (Nat.lt_succ_of_lt h)]

-- 16. For any natural number n, choosing n objects from n objects gives exactly one possible choice.
theorem choose_self (n : ℕ) : Nat.choose n n = 1 := by
  cases n with
  | zero => rw[Nat.choose_zero_right]
  | succ k => simp

-- 17. For any natural number n, choosing n+1 objects from n objects is impossible, so the number of ways is 0.
theorem choose_succ_self (n : ℕ) : Nat.choose n (Nat.succ n) = 0 := by
  induction n with
  | zero => rw[Nat.choose_zero_succ]
  | succ k ih => simp

-- 18. For any natural number n, choosing 1 object from n objects gives exactly n possible choices.
theorem choose_one_right (n : ℕ) : Nat.choose n 1 = n := by
  cases n with
  | zero => rw[Nat.choose_zero_succ]
  | succ k => rw[Nat.choose_succ_succ, Nat.choose_zero_right]
              simp
              rw[Nat.add_comm]

-- 19. For any natural number n, the value of (n+1)n/2 is equal to the value of n(n−1)/2 plus n, i.e., the triangular number for n+1 is the triangular number for n plus n.
theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  rw [← Nat.add_mul_div_left, Nat.mul_comm 2 n, ← Nat.mul_add, Nat.add_sub_cancel, Nat.mul_comm]
  cases n with
  | zero => rw[Nat.zero_add, Nat.zero_mul]
  | succ k => rw [Nat.succ_add, Nat.succ_sub_one]
  apply Nat.zero_lt_succ

-- 20. The factorial of 0 is equal to 1.
theorem factorial_zero : Nat.factorial 0 = 1 := by
  unfold Nat.factorial
  rfl

-- 21. For any natural number n, the factorial of n+1 is equal to n+1 multiplied by the factorial of n.
theorem factorial_succ (n : ℕ) : Nat.factorial (n + 1) = (n + 1) * Nat.factorial n := by
  induction n with
  | zero => rw[Nat.zero_add]
            unfold Nat.factorial
            rw[Nat.mul_one, Nat.factorial_zero, Nat.mul_one]
  | succ k ih => unfold Nat.factorial
                 rw[ih]

-- 22. The factorial of 2 is equal to 2.
theorem factorial_two : Nat.factorial 2 = 2 := by
  unfold Nat.factorial
  rw[Nat.factorial_one]

-- 23. If n ≠ 0, then n multiplied by the factorial of n−1 is equal to the factorial of n.
theorem mul_factorial_pred (hn : n ≠ 0) : n * Nat.factorial (n - 1) = Nat.factorial n := by
  cases n with
  | zero => contradiction
  | succ k => rw[Nat.succ_sub_one, Nat.factorial_succ]

-- 24. For any natural number n, the factorial of n is not equal to zero.
theorem factorial_ne_zero (n : ℕ) : Nat.factorial n ≠ 0 := by
  exact ne_of_gt (Nat.factorial_pos _)

-- 25. The factorial of a smaller or equal number always divides the factorial of a larger number.
theorem factorial_dvd_factorial {m n} (h : m ≤ n) : Nat.factorial m ∣ Nat.factorial n := by
  induction h with
  | refl => exact Nat.dvd_refl _
  | step _ ih => exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

-- 26. Every positive natural number m less than or equal to n is a divisor of n!.
theorem dvd_factorial : ∀ {m n}, 0 < m → m ≤ n → m ∣ Nat.factorial n := by
  intro m n h1 h2
  induction h2 with
  | refl => cases m with
            | zero => contradiction
            | succ k => rw [Nat.factorial_succ]
                        exact Nat.dvd_mul_right _ _
  | step _ ih => rw [Nat.factorial_succ]
                 exact Nat.dvd_trans ih (Nat.dvd_mul_left _ _)

-- 27. The factorial of a smaller or equal number is less than or equal to the factorial of a larger number.
theorem factorial_le {m n} (h : m ≤ n) : Nat.factorial m ≤ Nat.factorial n := by
  induction h with
  | refl => simp
  | step t ih => exact Nat.le_trans ih (Nat.factorial_le (Nat.le_succ _))

-- 28. For any natural numbers m and n, the product of m! and (m+1)^n is less than or equal to (m+n)!.
theorem factorial_mul_pow_le_factorial : ∀ {m n : ℕ}, Nat.factorial m * (m + 1) ^ n ≤ Nat.factorial (m + n) := by
  intro m n
  cases n with
  | zero => simp
  | succ t => rw [← Nat.add_assoc, factorial_succ, Nat.mul_comm (_ + 1), Nat.pow_succ, ← Nat.mul_assoc]
              exact Nat.mul_le_mul factorial_mul_pow_le_factorial (Nat.succ_le_succ (Nat.le_add_right _ _))

-- 29. The factorial of n is greater than 1 if and only if n is greater than 1.
theorem one_lt_factorial : 1 < Nat.factorial n ↔ 1 < n := by
  exact Nat.factorial_lt Nat.one_pos

-- 30. The factorial of n is equal to 1 if and only if n is less than or equal to 1.
theorem factorial_eq_one : Nat.factorial n = 1 ↔ n ≤ 1 := by
  constructor
  . intro h
    rw [← not_lt, ← one_lt_factorial, h]
    apply lt_irrefl
  · rintro (_ | _ | _) <;> rfl

-- 31. For every natural number n, n is less than or equal to its factorial
theorem self_le_factorial : ∀ n : ℕ, n ≤ Nat.factorial n := by
  intro n
  cases n with
  | zero => exact Nat.zero_le _
  | succ k => exact Nat.le_mul_of_pos_right _ (Nat.one_le_of_lt k.factorial_pos)

-- 32. For every natural number n, the factorial of n is less than or equal to n raised to the power n.
theorem factorial_le_pow : ∀ n, Nat.factorial n ≤ n ^ n := by
  intro n
  cases n with
  | zero => simp
  | succ k => calc
                Nat.factorial (k + 1) ≤ (k + 1) * k ^ k := by
                  rw [Nat.factorial_succ]
                  exact Nat.mul_le_mul_left _ (factorial_le_pow k)
                _ ≤ (k + 1) * (k + 1) ^ k := by
                  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ k) _)
                _ = (k + 1) ^ (k + 1) := by
                  rw [Nat.pow_succ]
                  rw [Nat.mul_comm]

-- 33. When you choose k objects from n objects and k is at most n, the number of ways to choose them is nonzero.
theorem choose_ne_zero {n k : ℕ} (h : k ≤ n) : n.choose k ≠ 0 := by
  exact (Nat.choose_pos h).ne'

-- 34. If k≤n, then choosing n−k objects from n objects gives the same number of ways as choosing k objects from n objects, i.e., symmetry property of binomial coefficients.
theorem choose_symm {n k : ℕ} (hk : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k := by
  rw [Nat.choose_eq_factorial_div_factorial hk, Nat.choose_eq_factorial_div_factorial (Nat.sub_le _ _), Nat.sub_sub_self hk, Nat.mul_comm]

