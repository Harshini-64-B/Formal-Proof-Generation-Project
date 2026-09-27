import Mathlib.Algebra.Group.Basic

namespace Algebra_Group

-- For any elements a and b of an additive commutative monoid M, and any natural number n, multiplying the sum (a + b) by n is equal to multiplying a by n and b by n, and then adding the results.
theorem nsmul_add {M : Type u_4} [AddCommMonoid M] (a b : M) (n : ℕ) : n • (a + b) = n • a + n • b := by
  induction n with
  | zero => simp
  | succ n ih => repeat rw [succ_nsmul]
                 rw[ih, add_assoc, add_assoc, add_comm _ b, ←add_assoc a _, add_comm a, add_assoc, add_comm a b]

end Algebra_Group
