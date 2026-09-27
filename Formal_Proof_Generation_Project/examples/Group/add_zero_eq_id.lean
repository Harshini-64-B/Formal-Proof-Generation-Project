import Mathlib.Algebra.Group.Basic

namespace Algebra_Group

-- For any type M that has an addition operation with zero, the function that adds 0 to an element is equal to the identity function.
theorem add_zero_eq_id {M : Type u_4} [AddZeroClass M] : (fun (x : M) => x + 0) = id := by
  funext a
  rw[add_zero]
  unfold id
  rfl

end Algebra_Group
