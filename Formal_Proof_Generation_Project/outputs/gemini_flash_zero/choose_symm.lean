An elegant and self-contained proof of the theorem in Lean 4, using the relation between the binomial coefficient and factorials:

```lean
import Mathlib.Data.Nat.Choose.Basic

theorem choose_symm {n k : ℕ} (hk : k ≤ n) : Nat.choose n (n - k) = Nat.choose n k := by
  have h1 : Nat.choose n (n - k) * ((n - k).factorial * k.factorial) = n.factorial := by
    have h_sub : n - (n - k) = k := Nat.sub_sub_self hk
    have h_choose := Nat.choose_mul_factorial_mul_factorial (Nat.sub_le n k)
    rw [h_sub] at h_choose
    rw [← h_choose]
    ring
  have h2 : Nat.choose n k * ((n - k).factorial * k.factorial) = n.factorial := by
    have h_choose := Nat.choose_mul_factorial_mul_factorial hk
    rw [← h_choose]
    ring
  have h3 : Nat.choose n (n - k) * ((n - k).factorial * k.factorial) = Nat.choose n k * ((n - k).factorial * k.factorial) := by
    rw [h1, h2]
  exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (Nat.factorial_pos (n - k)) (Nat.factorial_pos k)) h3
