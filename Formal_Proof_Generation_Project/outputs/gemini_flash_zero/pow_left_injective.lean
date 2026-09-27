theorem pow_left_injective {n : Nat} (hn : n ≠ 0) : Function.Injective fun (a : Nat) => a ^ n :=
  (Nat.strictMono_pow hn).injective