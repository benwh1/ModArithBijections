import Mathlib.FieldTheory.Finite.Basic
import ModArithBijections.Helper

def f (a b x : ℕ) : ℕ := a * b ^ x + x

noncomputable def order (m n : ℕ) := orderOf (n : ZMod m)

@[simp]
noncomputable def seq b m n := match n with
  | 0 => m
  | Nat.succ k => order (seq b m k) b

lemma order_lt {m} (hm : m > 1) (hcoprime : Nat.Coprime b m) : order m b < m := by
  have ⟨k, hk1, hkm, hk⟩ : ∃ k, 1 <= k ∧ k < m ∧ b^k ≡ 1 [MOD m] := by
    use Nat.totient m
    have hm0 : m > 0 := Nat.zero_lt_of_lt hm
    apply And.intro
    { exact Nat.totient_pos hm0 }
    {
      apply And.intro
      { apply Nat.totient_lt _ hm }
      { apply Nat.ModEq.pow_totient hcoprime }
    }
  apply (ZMod.eq_iff_modEq_nat m).mpr at hk
  simp at hk
  have hk : order m b <= k := orderOf_le_of_pow_eq_one hk1 hk
  exact Nat.lt_of_le_of_lt hk hkm

lemma order_dvd {m x} (hx : b^x ≡ 1 [MOD m]) : order m b ∣ x := by
  unfold order
  have h : (b : ZMod m)^x = 1 := by
    apply (ZMod.eq_iff_modEq_nat m).mpr at hx
    simp at hx
    exact hx
  exact orderOf_dvd_of_pow_eq_one h

lemma pow_ndvd {m k} (hk : k > 0) (h : b^k ≡ 1 [MOD m]) : Nat.Coprime b m := by
  have hk1 : k.pred + 1 = k := Nat.succ_pred_eq_of_pos hk
  apply Nat.coprime_of_mul_modEq_one (b^k.pred)
  rw [mul_comm]
  have h1 := pow_add b (k.pred) 1
  simp at h1
  rw [← h1, hk1]
  exact h

lemma seq_pow_mod_prev b m k : b^seq b m k.succ ≡ 1 [MOD seq b m k] := by
  apply (ZMod.eq_iff_modEq_nat _).mp
  simp
  apply pow_orderOf_eq_one

lemma order_iter {b m} (h : b^m ≡ 1 [MOD m]) : b^order m b ≡ 1 [MOD order m b] := by
  have hm : b^order m b ≡ 1 [MOD m] := seq_pow_mod_prev b m 0
  have ⟨k, hk⟩ : order m b ∣ m := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    have h1 := (ZMod.eq_iff_modEq_nat m).mpr h
    simp at h1
    exact h1
  nth_rewrite 1 [hk] at hm
  exact Nat.ModEq.of_mul_right k hm

lemma seq_pow_one {b m} (h : b^m ≡ 1 [MOD m]) : ∀ k, b^seq b m k ≡ 1 [MOD seq b m k] := by
  intro k
  induction' k with k hk
  { exact h }
  { exact order_iter hk }

lemma seq_dvd_prev {b m} (h : b^m ≡ 1 [MOD m]) : ∀ k, seq b m k.succ ∣ seq b m k := by
  intro k
  simp
  apply order_dvd
  apply seq_pow_one h

lemma seq_dvd_seq_zero {b m} (h : b^m ≡ 1 [MOD m]) : ∀ k, seq b m k ∣ m := by
  intro k
  induction' k with k hk
  { simp }
  {
    have h1 := seq_dvd_prev h k
    exact Nat.dvd_trans h1 hk
  }

lemma seq_pos {b m} (hm : m > 0) (h : b^m ≡ 1 [MOD m]) : ∀ k, seq b m k > 0 := by
  intro k
  induction' k with k hk
  { exact hm }
  {
    simp
    have hpow : (b : ZMod (seq b m k))^seq b m k = 1 := by
      have h1 := seq_pow_one h k
      have h2 := (ZMod.eq_iff_modEq_nat _).mpr h1
      simp at h2
      exact h2
    have hpow' : b^seq b m k ≡ 1 [MOD seq b m k] := by
      apply (ZMod.eq_iff_modEq_nat (seq b m k)).mp
      simp
      exact hpow
    have hcoprime : Nat.Coprime b (seq b m k) := pow_ndvd hk hpow'
    let three := ZMod.unitOfCoprime b hcoprime
    have _ : NeZero (seq b m k) := NeZero.of_gt hk
    have _ : Finite (ZMod (seq b m k)) := by
      apply Fintype.finite
      apply ZMod.fintype
    have h := orderOf_pos three
    rw [← orderOf_units] at h
    exact h
  }

lemma seq_dec {b m k} (hm : m > 0) (h : b^m ≡ 1 [MOD m]) (hg1 : seq b m k > 1)
  : seq b m k.succ < seq b m k := by
  have hcoprime : Nat.Coprime b (seq b m k) := by
    apply pow_ndvd hm
    have ⟨d, hd⟩ := seq_dvd_seq_zero h k
    nth_rewrite 1 [hd] at h
    exact Nat.ModEq.of_mul_right d h
  apply order_lt hg1 hcoprime

lemma seq_lt_seq_zero {b m} (hm : m > 0) (h : b^m ≡ 1 [MOD m]) : ∀ k, seq b m k <= m := by
  intro k
  have hdvd := seq_dvd_seq_zero h k
  exact Nat.le_of_dvd hm hdvd

lemma seq_one_next {b m} (h : seq b m k = 1) : seq b m k.succ = 1 := by
  simp
  rw [h]
  unfold order
  simp

lemma seq_one {b m} (hmgt : m > 0) (hm : b^m ≡ 1 [MOD m]) : ∃ k, seq b m k = 1 := by
  let r := Nat.lt
  let C := fun x => ∃ k, seq b m k <= x
  have : WellFounded r := by apply Nat.lt_wfRel.wf
  have well_ordering := @WellFounded.induction_bot ℕ r this m 1 C
  unfold_let at well_ordering
  simp at well_ordering

  have seq_le_1 : ∃ k, seq b m k <= 1 := by
    apply well_ordering
    {
      intro u hu x hx
      use (seq b m x.succ)
      apply And.intro
      {
        have h0 : ∀ n, n = 0 ∨ n = 1 ∨ n > 1 := by
          intro n
          cases' n with n
          { simp }
          { cases' n with n; repeat simp }
        cases' h0 (seq b m x) with h0 h1
        {
          have h1 := seq_pos hmgt hm x
          rw [h0] at h1
          contradiction
        }
        {
          cases' h1 with h1 hg1
          {
            rw [seq_one_next h1]
            rw [h1] at hx
            exact Ne.lt_of_le' hu hx
          }
          {
            have hxs : seq b m x.succ < seq b m x := seq_dec hmgt hm hg1
            exact Nat.lt_of_lt_of_le hxs hx
          }
        }
      }
      use x.succ
    }
    { apply seq_lt_seq_zero hmgt hm }
    { exact 0 }
  have ⟨l, hl⟩ := seq_le_1
  have hseq_pos : seq b m l > 0 := seq_pos hmgt hm l
  use l
  exact Nat.le_antisymm hl hseq_pos

lemma iterate' {a b m x y : ℕ} (hmgt : m > 0) (hf : f a b x ≡ f a b y [MOD m]) (hm : b^m ≡ 1 [MOD m])
  (h : x ≡ y [MOD order m b]) : x ≡ y [MOD m] := by
  wlog hge : x >= y
  {
    have hyx : y >= x := Nat.le_of_not_le hge
    apply Nat.ModEq.symm at hf
    apply Nat.ModEq.symm at h
    apply Nat.ModEq.symm
    exact this hmgt hf hm h hyx
  }

  unfold f at hf
  let d := order m b

  have hdgt : d > 0 := seq_pos hmgt hm 1
  have ⟨t, hdt⟩ : ∃ t, x = y + t * d := (Helper.add_fac_iff_mod hdgt hge).mp h
  have hbdm : b^d ≡ 1 [MOD m] := seq_pow_mod_prev b m 0
  have habxym : a * b^x ≡ a * b^y [MOD m] := by
    rw [hdt, pow_add]
    have h0 : b^y = b^y * 1^t := by simp
    nth_rewrite 2 [h0]
    repeat apply Nat.ModEq.mul_left
    rw [mul_comm, pow_mul]
    exact Nat.ModEq.pow t hbdm

  exact Nat.ModEq.add_left_cancel habxym hf

lemma iterate {a b m x y k : ℕ} (hmgt : m > 0) (hm : b^m ≡ 1 [MOD m]) (hf : f a b x ≡ f a b y [MOD m])
  (h : x ≡ y [MOD seq b m k.succ]) : x ≡ y [MOD seq b m k] := by
  have hsmk : b^seq b m k ≡ 1 [MOD seq b m k] := seq_pow_one hm k
  have hpos : seq b m k > 0 := seq_pos hmgt hm k
  have hdvd : seq b m k ∣ m := seq_dvd_seq_zero hm k
  have hfsmk : f a b x ≡ f a b y [MOD seq b m k] := by
    have ⟨d, hd⟩ := hdvd
    nth_rewrite 1 [hd] at hf
    exact Nat.ModEq.of_mul_right d hf
  exact iterate' hpos hfsmk hsmk h

theorem bijection_mod_m {a b m x y : ℕ} (hmgt : m > 0) (hm : b^m ≡ 1 [MOD m]) (hf : f a b x ≡ f a b y [MOD m])
  : x ≡ y [MOD m] := by
  have hxy1 : x ≡ y [MOD 1] := Nat.modEq_one
  have ⟨idx, hidx⟩ := seq_one hmgt hm

  let r := Nat.lt
  let C := fun k => x ≡ y [MOD seq b m k]
  have : WellFounded r := by apply Nat.lt_wfRel.wf
  have well_ordering := @WellFounded.induction_bot ℕ r this idx 0 C

  apply well_ordering
  {
    intro b hb hcb
    have ⟨b1, hb1⟩ : ∃ b1, b = Nat.succ b1 := Nat.exists_eq_succ_of_ne_zero hb
    use b1
    unfold_let
    simp
    apply And.intro
    { rw [hb1]; simp }
    {
      unfold_let at hcb
      rw [hb1] at hcb
      exact iterate hmgt hm hf hcb
    }
  }
  {
    unfold_let
    simp
    rw [hidx]
    exact hxy1
  }
