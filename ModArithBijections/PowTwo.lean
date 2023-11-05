import ModArithBijections.ModM

lemma three_pow_two_pow_k : ∀ k, 3^2^k ≡ 1 [MOD 2^(k+1)] := by
  intro k
  apply (Helper.add_fac_iff_mod (Nat.one_le_pow' _ _) (Nat.one_le_pow' _ _)).mpr

  induction' k with k hind
  { use 1; simp }
  {
    have ⟨t, ht⟩ := hind
    use t * (1 + t * 2^k)
    rw [Nat.succ_eq_add_one, pow_add, pow_mul, ht]
    ring
  }

lemma three_pow_two_pow_k' : ∀ k, 3^2^k ≡ 1 [MOD 2^k] := by
  intro k
  have h := three_pow_two_pow_k k
  exact Nat.ModEq.of_mul_right 2 h

theorem bijection_mod_pow_two {x y k} (hf : f x ≡ f y [MOD 2^k]) : x ≡ y [MOD 2^k] :=
  bijection_mod_m (Nat.one_le_pow' _ _) (three_pow_two_pow_k' k) hf
