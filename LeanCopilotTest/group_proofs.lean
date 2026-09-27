import LeanCopilot
import Mathlib.Algebra.Group.Basic

namespace Algebra_group
-- 1. In a semigroup, composing left multiplication by y with left multiplication by x is the same as left multiplication by x * y.
theorem comp_mul_left {α : Type u_1} [Semigroup α] (x y : α) : ((fun (x_1 : α) => x * x_1) ∘ fun (x : α) => y * x) = fun (x_1 : α) => x * y * x_1 := by
  simp

-- 2. In an additive semigroup, composing addition on the left by y followed by addition on the left by x is equivalent to addition on the left by x + y.
theorem comp_add_left {α : Type u_1} [AddSemigroup α] (x y : α) : ((fun (x_1 : α) => x + x_1) ∘ fun (x : α) => y + x) = fun (x_1 : α) => x + y + x_1 := by
  simp

-- 3. If the sum of a and b is zero, then a is zero if and only if b is zero.
theorem eq_zero_iff_eq_zero_of_add_eq_zero {M : Type u_4} [AddZeroClass M] {a b : M} (h : a + b = 0) : a = 0 ↔ b = 0 := by
  constructor
  . intro h'
    rw[h'] at h
    rw [zero_add] at h
    exact h
  . intro h'
    rw[h'] at h
    rw [add_zero] at h
    exact h

-- 4. If the product of two elements a and b is equal to 1, then a is equal to 1 if and only if b is equal to 1.
theorem eq_one_iff_eq_one_of_mul_eq_one {M : Type u_4} [MulOneClass M] {a b : M} (h : a * b = 1) :a = 1 ↔ b = 1 := by
  constructor
  . intro h1
    rw[h1, one_mul] at h
    exact h
  . intro h1
    rw[h1, mul_one] at h
    exact h

-- 5. Multiplying any element by the multiplicative identity 1 on the left leaves the element unchanged.
theorem one_mul_eq_id {M : Type u_4} [MulOneClass M] : (fun (x : M) => 1 * x) = id := by
  funext a
  rw[one_mul]
  unfold id
  rfl

-- 6. Adding the additive identity 0 to any element on the left leaves the element unchanged.
theorem zero_add_eq_id {M : Type u_4} [AddZeroClass M] : (fun (x : M) => 0 + x) = id := by
  funext a
  rw[zero_add]
  unfold id
  rfl

-- 7. In a commutative semigroup, the left factors of a product can be interchanged without changing the result.
theorem mul_left_comm {G : Type u_3} [CommSemigroup G] (a b c : G) : a * (b * c) = b * (a * c) := by
  rw[mul_comm, mul_assoc, mul_comm c a]

-- 8. In an additive commutative semigroup, the first two elements in a sum can be interchanged without changing the result.
theorem add_left_comm {G : Type u_3} [AddCommSemigroup G] (a b c : G) : a + (b + c) = b + (a + c) := by
  rw[add_comm, add_assoc, add_comm c a]

-- 9. In a commutative semigroup, the middle two factors in a product can be interchanged without changing the result.
theorem mul_mul_mul_comm {G : Type u_3} [CommSemigroup G] (a b c d : G) : a * b * (c * d) = a * c * (b * d) := by
  rw[mul_assoc, mul_comm b, mul_assoc, mul_comm d b, ← mul_assoc]

-- 10. In an additive commutative semigroup, the middle two terms in a sum can be interchanged without changing the result.
theorem add_add_add_comm {G : Type u_3} [AddCommSemigroup G] (a b c d : G) : a + b + (c + d) = a + c + (b + d) := by
  rw[add_assoc, add_comm b, add_assoc, add_comm d b, ← add_assoc]

-- 11. In a commutative semigroup, the factors of a product can be cyclically rotated without changing the result.
theorem mul_rotate {G : Type u_3} [CommSemigroup G] (a b c : G) : a * b * c = b * c * a := by
  rw[mul_assoc, mul_comm]

-- 12. In an additive commutative semigroup, the terms of a sum can be cyclically rotated without changing the result.
theorem add_rotate {G : Type u_3} [AddCommSemigroup G] (a b c : G) : a + b + c = b + c + a := by
  rw[add_assoc, add_comm]

-- 13. For an element a of a monoid, raising a to the power 1 when a proposition P is true and to the power 0 when P is false gives a when P is true and 1 when P is false.
theorem pow_boole {M : Type u_4} [Monoid M] (P : Prop) [Decidable P] (a : M) : (a ^ if P then 1 else 0) = if P then a else 1 := by
  split_ifs with h
  . rw[pow_one]
  . rw[pow_zero]

-- 14. If P is true, then multiplying a by 1 using repeated addition gives a; if P is false, multiplying a by 0 gives 0.
theorem boole_nsmul {M : Type u_4} [AddMonoid M] (P : Prop) [Decidable P] (a : M) : (if P then 1 else 0) • a = if P then a else 0 := by
  split_ifs with h
  . exact one_nsmul a
  . exact zero_nsmul a

-- 15. For an element a of a monoid, if m≤n, then multiplying a^m by a^(n−m) gives a^n.
theorem pow_mul_pow_sub {M : Type u_4} [Monoid M] {m n : ℕ} (a : M) (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← pow_add, Nat.add_comm, Nat.sub_add_cancel h]

-- 16. If n is a nonzero natural number and a is an element of a monoid, then multiplying a by a raised to the power n − 1 gives a raised to the power n.
theorem mul_pow_sub_one {M : Type u_4} [Monoid M] {n : ℕ} (hn : n ≠ 0) (a : M) : a * a ^ (n - 1) = a ^ n := by
  rw [← pow_succ', Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 hn)]

-- 17. If a is an element of a monoid and a^n=1, then for any natural number m, a^m=a^(m mod n).
theorem pow_eq_pow_mod {M : Type u_4} [Monoid M] {a : M} {n : ℕ} (m : ℕ) (ha : a ^ n = 1) : a ^ m = a ^ (m % n) := by
  calc
    a ^ m = a ^ (m % n + n * (m / n)) := by rw [Nat.mod_add_div]
    _ = a ^ (m % n) := by simp [pow_add, pow_mul, ha]

-- 18. If a and b are elements of a monoid and a * b = 1, then for any natural number n, a ^ n * b ^ n = 1.
theorem pow_mul_pow_eq_one {M : Type u_4} [Monoid M] {a b : M} (n : ℕ) : a * b = 1 → a ^ n * b ^ n = 1 := by
  intro h
  induction n with
  | zero => rw[pow_zero, pow_zero, one_mul]
  | succ n ih => calc
                  a ^ n.succ * b ^ n.succ = a ^ n * a * (b * b ^ n) := by rw [pow_succ, pow_succ']
                  _ = a ^ n * (a * b) * b ^ n := by simp only [mul_assoc]
                  _ = 1 := by rw [h, mul_one, ih]

-- 19. In a commutative monoid, if both y and z multiply with x to give 1, then y and z are equal.
theorem inv_unique {M : Type u_4} [CommMonoid M] {x y z : M} (hy : x * y = 1) (hz : x * z = 1) : y = z := by
  exact left_inv_eq_right_inv (Trans.trans (mul_comm _ _) hy) hz

-- 20. In an additive commutative monoid, if both y and z add to x to give 0, then y and z are equal.
theorem neg_unique {M : Type u_4} [AddCommMonoid M] {x y z : M} (hy : x + y = 0) (hz : x + z = 0) : y = z := by
  exact left_neg_eq_right_neg (Trans.trans (add_comm _ _) hy) hz

-- 21. In a commutative monoid, the power of a product is equal to the product of the powers.
theorem mul_pow {M : Type u_4} [CommMonoid M] (a b : M) (n : ℕ) : (a * b) ^ n = a ^ n * b ^ n := by
  induction n with
  | zero => repeat rw[pow_zero]
            rw[mul_one]
  | succ k ih => rw[pow_add, pow_one, ih, mul_assoc, mul_comm a b, mul_comm, ← mul_assoc, ← pow_succ, mul_assoc, mul_comm, ← pow_succ']

-- 22. In a left-cancellative monoid, a×b=a if and only if b=1.
theorem mul_eq_left {M : Type u_4} [Monoid M] [IsLeftCancelMul M] {a b : M} : a * b = a ↔ b = 1 := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 23. In a left-cancellative additive monoid, a = a + b if and only if b = 0.
theorem left_eq_add {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a = a + b ↔ b = 0 := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

-- 24. In a left-cancellative additive monoid, a + b ≠ a if and only if b ≠ 0.
theorem add_ne_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b ≠ a ↔ b ≠ 0 := by
  constructor
  . intro h
    simp at h
    simp
    exact h
  . intro h
    simp at h
    simp
    exact h

-- 25. In a cancellative commutative monoid, if a * b = c * d, then a = c if and only if b = d.
theorem eq_iff_eq_of_mul_eq_mul {α : Type u_1} [CancelCommMonoid α] {a b c d : α} (h : a * b = c * d) : a = c ↔ b = d := by
  constructor
  . intro h1
    rw[h1] at h
    simp at h
    exact h
  . intro h1
    rw[h1] at h
    simp at h
    exact h

-- 26. In a DivInvMonoid, multiplying x by 1 / y is equal to dividing x by y.
theorem mul_one_div {G : Type u_3} [DivInvMonoid G] (x y : G) : x * (1 / y) = x / y := by
  rw [div_eq_mul_inv, one_mul, div_eq_mul_inv]

-- 27. In a DivInvMonoid, multiplying a by b / c is equal to multiplying a by b and then dividing the result by c.
theorem mul_div_assoc' {G : Type u_3} [DivInvMonoid G] (a b c : G) : a * (b / c) = a * b / c := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_assoc]

-- 28. In a subtraction monoid, the negative of a minus b is equal to the negative of b + a.
theorem neg_sub_left {α : Type u_1} [SubtractionMonoid α] (a b : α) : -a - b = -(b + a) := by
  rw [sub_eq_add_neg]
  simp

-- 29. In a subtraction monoid, the n-fold addition of the negation of a is equal to the negation of the n-fold addition of a.
theorem neg_nsmul {α : Type u_1} [SubtractionMonoid α] (a : α) (n : ℕ) : n • -a = -(n • a) := by
  simp

-- 30. In a division commutative monoid, dividing a by b * c is equal to dividing a by b and then multiplying by 1 / c.
theorem div_mul_eq_div_mul_one_div {α : Type u_1} [DivisionCommMonoid α] (a b c : α) : a / (b * c) = a / b * (1 / c) := by
  repeat rw [div_eq_mul_inv]
  rw[one_mul, mul_assoc, mul_inv_rev]
  rw [mul_comm c⁻¹ b⁻¹]

-- 31. In a division commutative monoid, dividing a by b, and then dividing the result by c / d, is equal to a * d divided by b * c.
theorem div_div_div_eq {α : Type u_1} [DivisionCommMonoid α] (a b c d : α) : a / b / (c / d) = a * d / (b * c) := by
  repeat rw [div_eq_mul_inv]
  repeat rw[mul_inv_rev]
  rw[inv_inv, mul_assoc, mul_comm d]
  simp [mul_assoc, mul_comm, mul_left_comm]

-- 32. In a subtraction commutative monoid, a + b - (c + d) is equal to a - c + (b - d).
theorem add_sub_add_comm {α : Type u_1} [SubtractionCommMonoid α] (a b c d : α) : a + b - (c + d) = a - c + (b - d) := by
  repeat rw [sub_eq_add_neg]
  rw [add_assoc, neg_add]
  simp [add_assoc, add_left_comm]

-- 33. In an additive group, a - b = -b if and only if a = 0.
theorem sub_eq_neg_self {G : Type u_3} [AddGroup G] {a b : G} : a - b = -b ↔ a = 0 := by
  constructor
  . intro h
    simp at h
    exact h
  . intro h
    simp
    exact h

end Algebra_group
