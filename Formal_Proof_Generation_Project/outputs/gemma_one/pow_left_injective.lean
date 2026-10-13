theorem pow_left_injective {n : Nat} (hn : n ≠ 0) : Function.Injective fun (a : Nat) => a ^ n := by
  intro a b h
  have h_lt : ∀ (x y : ℕ), x < y → x ^ n < y ^ n := by
    intro x y h_xy
    have h_all : ∀ m, m > 0 → x < y → x ^ m < y ^ m := by
      intro m hm h_xy
      induction m with
      | zero => contradiction
      | succ m' ih =>
        if h_m_one : m' = 0 then
        begin
          simp [h_m_one] at h_m_one
          exact h_xy
        end
        else
        begin
          have h_m_prime_pos : m' > 0 := by simp [h_m_one] at h_m_one; exact hm
          if h_x_zero : x = 0 then
          begin
            rw [h_x_zero] at h_xy
            simp [h_x_zero]
            have h_y_pos : y > 0 := Nat.succ_pos _
            have h_y_pow_pos : y ^ (m' + 1) > 0 := Nat.pow_pos h_y_pos (Nat.succ_pos m')
            exact h_y_pow_pos
          end
          else
          begin
            have h_x_pos : x > 0 := Nat.succ_pos _
            have h_xm_pos : x ^ m' > 0 := Nat.pow_pos h_x_pos h_m_prime_pos
            have h_ih_val : x ^ m' < y ^ m' := ih h_m_prime_pos h_xy
            have h_step1 : x * x ^ m' < y * x ^ m' := Nat.mul_lt_mul_left h_xy h_xm_pos
            have h_step2 : y * x ^ m' < y * y ^ m' := Nat.mul_lt_mul_right h_ih_val (Nat.succ_pos _)
            rw [Nat.pow_succ] at h_step1
            rw [Nat.pow_succ] at h_step2
            exact h_step1.trans h_step2
          end
        end
    exact h_all n hn h_xy
  by_contra h_ne
  cases h_ne with
  | intro h_lt_gt h_gt_lt =>
    have h_xy : a < b := h_lt_gt
    have h_yx : b < a := h_gt_lt
    have h_pow_xy : a ^ n < b ^ n := h_lt a b h_xy
    have h_pow_yx : b ^ n < a ^ n := h_lt b a h_yx
    exact Nat.lt_irrefl (a ^ n) (h_pow_xy.trans h_pow_yx)