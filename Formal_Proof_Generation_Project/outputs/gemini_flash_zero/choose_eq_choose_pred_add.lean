import Mathlib.Data.Nat.Choose.Basic

theorem choose_eq_choose_pred_add {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    Nat.choose n k = Nat.choose (n - 1) (k - 1) + Nat.choose (n - 1) k := by
  have hn' : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
  have hk' : k = k - 1 + 1 := (Nat.sub_add_cancel hk).symm
  nth_rw 1 [hn']
  nth_rw 1 [hk']
  rw [Nat.choose_succ_succ, ← hk']