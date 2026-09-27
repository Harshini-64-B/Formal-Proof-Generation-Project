import Mathlib.Algebra.Group.Basic

namespace Algebra_Group

theorem add_eq_left {M : Type u_4} [AddMonoid M] [IsLeftCancelAdd M] {a b : M} : a + b = a ↔ b = 0 := by
  constructor
  · intro h
    apply add_left_cancel (a := a)
    simpa using h.symm
  · intro h
    simpa

end Algebra_Group
