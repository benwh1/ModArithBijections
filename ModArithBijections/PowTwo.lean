import ModArithBijections.ModM

lemma odd_pow_two_pow_k {b : ℕ} (hb : Odd b) : ∀ k, b^2^k ≡ 1 [MOD 2^(k+1)] := by
  intro k
  have ⟨l, hl⟩ := hb
  have hb2kpos : b^2^k > 0 := by
    rw [hl]
    apply Nat.one_le_pow' _ (2 * l)
  apply (Helper.add_fac_iff_mod (Nat.one_le_pow' _ _) hb2kpos).mpr

  clear hb2kpos

  induction' k with k hind
  {
    use l;
    rw [hl];
    simp;
    ring
  }
  {
    have ⟨t, ht⟩ := hind
    use t * (1 + t * 2^k)
    rw [Nat.succ_eq_add_one, pow_add, pow_mul, ht]
    ring
  }

lemma odd_pow_two_pow_k' {b : ℕ} (hb : Odd b) : ∀ k, b^2^k ≡ 1 [MOD 2^k] := by
  intro k
  have h := odd_pow_two_pow_k hb k
  exact Nat.ModEq.of_mul_right 2 h

theorem bijection_mod_pow_two {a b c k x y} (hb : Odd b) (hc : Nat.Coprime c (2^k))
  (hf : f a b c x ≡ f a b c y [MOD 2^k]) : x ≡ y [MOD 2^k] :=
  bijection_mod_m (Nat.one_le_pow' _ _) (odd_pow_two_pow_k' hb k) hc hf
