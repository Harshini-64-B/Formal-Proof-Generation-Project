theorem factorial_pos (n : 1 ≤ n) : 0 < n.factorial := by
  rcases n with _ | n
  · contradiction
  · exact Nat.factorial_pos n