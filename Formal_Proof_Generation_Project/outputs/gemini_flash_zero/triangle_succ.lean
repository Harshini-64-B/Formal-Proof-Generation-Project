An elegant proof of the theorem in Lean 4:

```lean
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Omega

theorem triangle_succ (n : ℕ) : (n + 1) * (n + 1 - 1) / 2 = n * (n - 1) / 2 + n := by
  cases n with
  | zero => rfl
  | succ n =>
    have h1 : n + 1 + 1 - 1 = n + 1 := by omega
    have h2 : n + 1 - 1 = n := by omega
    rw [h1, h2]
    have h3 : (n + 1 + 1) * (n + 1) = (n + 1) * n + (n + 1) * 2 := by ring
    rw [h3]
    rw [Nat.add_mul_div_right ((n + 1) * n) (n + 1) (by decide)]