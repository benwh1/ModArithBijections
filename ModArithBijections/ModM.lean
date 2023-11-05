import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Parity
import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Init.Function
import Mathlib.Order.RelClasses
import Mathlib.Tactic.NormNum.Core
import ModArithBijections.Basic

noncomputable def order (m n : ℕ) := orderOf (n : ZMod m)

@[simp]
noncomputable def seq m n := match n with
  | 0 => m
  | Nat.succ k => order (seq m k) 3

lemma order_lt {m} (hm : m > 1) (hcoprime : Nat.Coprime 3 m) : order m 3 < m := by
  have ⟨k, hk1, hkm, hk⟩ : ∃ k, 1 <= k ∧ k < m ∧ 3^k ≡ 1 [MOD m] := by
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
  have hk : order m 3 <= k := orderOf_le_of_pow_eq_one hk1 hk
  exact Nat.lt_of_le_of_lt hk hkm

lemma order_dvd {m x} (hx : 3^x ≡ 1 [MOD m]) : order m 3 ∣ x := by
  unfold order
  simp
  have h : (3 : ZMod m)^x = 1 := by
    apply (ZMod.eq_iff_modEq_nat m).mpr at hx
    simp at hx
    exact hx
  exact orderOf_dvd_of_pow_eq_one h

lemma pow_ndvd {m a} (ha : a > 0) (h : 3^a ≡ 1 [MOD m]) : Nat.Coprime 3 m := by
  have hprime : Nat.Prime 3 := by norm_num
  apply (Nat.Prime.coprime_iff_not_dvd hprime).mpr
  intro hdvd

  have ⟨k, hk⟩ := hdvd
  rw [hk] at h
  apply Nat.ModEq.of_mul_right at h
  have hdvd2 : 3 ∣ 3^a := pow_dvd_pow 3 ha
  have h0 := Nat.modEq_zero_iff_dvd.mpr hdvd2
  have h01 := Nat.ModEq.trans (h.symm) h0
  simp at h01

lemma seq_pow_mod_prev m k : 3^seq m k.succ ≡ 1 [MOD seq m k] := by
  apply (ZMod.eq_iff_modEq_nat _).mp
  simp
  apply pow_orderOf_eq_one

lemma order_iter {m} (h : 3^m ≡ 1 [MOD m]) : 3^order m 3 ≡ 1 [MOD order m 3] := by
  have hm : 3^order m 3 ≡ 1 [MOD m] := seq_pow_mod_prev m 0
  have ⟨k, hk⟩ : order m 3 ∣ m := by
    apply orderOf_dvd_iff_pow_eq_one.mpr
    simp
    have h1 := (ZMod.eq_iff_modEq_nat m).mpr h
    simp at h1
    exact h1
  nth_rewrite 1 [hk] at hm
  exact Nat.ModEq.of_mul_right k hm

lemma seq_pow_one {m} (h : 3^m ≡ 1 [MOD m]) : ∀ k, 3^seq m k ≡ 1 [MOD seq m k] := by
  intro k
  induction' k with k hk
  { exact h }
  { exact order_iter hk }

lemma seq_dvd_prev {m} (h : 3^m ≡ 1 [MOD m]) : ∀ k, seq m k.succ ∣ seq m k := by
  intro k
  simp
  apply order_dvd
  apply seq_pow_one h

lemma seq_dvd_seq_zero {m} (h : 3^m ≡ 1 [MOD m]) : ∀ k, seq m k ∣ m := by
  intro k
  induction' k with k hk
  { simp }
  {
    have h1 := seq_dvd_prev h k
    exact Nat.dvd_trans h1 hk
  }

lemma seq_pos {m} (hm : m > 0) (h : 3^m ≡ 1 [MOD m]) k : seq m k > 0 := by
  induction' k with k hk
  { exact hm }
  {
    simp
    have hpow : (3 : ZMod (seq m k))^seq m k = 1 := by
      have h1 := seq_pow_one h k
      have h2 := (ZMod.eq_iff_modEq_nat _).mpr h1
      simp at h2
      exact h2
    have hpow' : 3^seq m k ≡ 1 [MOD seq m k] := by
      apply (ZMod.eq_iff_modEq_nat (seq m k)).mp
      simp
      exact hpow
    have hcoprime : Nat.Coprime 3 (seq m k) := pow_ndvd hk hpow'
    let three := ZMod.unitOfCoprime 3 hcoprime
    have _ : NeZero (seq m k) := NeZero.of_gt hk
    have _ : Finite (ZMod (seq m k)) := by
      apply Fintype.finite
      apply ZMod.fintype
    have h := orderOf_pos three
    unfold order; simp
    have heq : orderOf three = orderOf (3 : ZMod (seq m k)) := by
      apply orderOf_units.symm
    rw [← heq]
    exact h
  }

lemma seq_dec {m} (hm : m > 0) (h : 3^m ≡ 1 [MOD m]) {k} (hg1 : seq m k > 1)
  : seq m k.succ < seq m k := by
  have hcoprime : Nat.Coprime 3 (seq m k) := by
    apply pow_ndvd hm
    have ⟨d, hd⟩ := seq_dvd_seq_zero h k
    nth_rewrite 1 [hd] at h
    exact Nat.ModEq.of_mul_right d h
  apply order_lt hg1 hcoprime

lemma seq_lt_seq_zero {m} (hm : m > 0) (h : 3^m ≡ 1 [MOD m])
  : ∀ k, seq m k <= m := by
  intro k
  have hdvd := seq_dvd_seq_zero h k
  exact Nat.le_of_dvd hm hdvd

lemma seq_one_next {m} (h : seq m k = 1) : seq m k.succ = 1 := by
  simp
  rw [h]
  unfold order
  simp

lemma seq_zero_next {m} (h : seq m k = 0) : seq m k.succ = 0 := by
  simp
  rw [h]
  unfold order
  simp
  apply orderOf_eq_zero_iff.mpr
  intro hfin
  unfold IsOfFinOrder at hfin
  unfold Function.periodicPts at hfin
  simp at hfin
  have ⟨n, ⟨hn0, hn⟩⟩ := hfin
  unfold Function.IsPeriodicPt Function.IsFixedPt at hn
  simp at hn
  have hn : (↑(3^n) : ZMod 0) = 1 := by simp; apply hn
  have hn := (ZMod.eq_iff_modEq_nat _).mp hn
  simp at hn
  have hn : 3^n = 3^0 := hn
  have hneq0 := Nat.pow_right_injective (by norm_num) hn
  rw [hneq0] at hn0
  exact LT.lt.false hn0

lemma seq_one {m} (hm : m > 0) (h : 3^m ≡ 1 [MOD m])
  : ∃ k, seq m k = 1 := by
  let r := Nat.lt
  let C := fun x => ∃ k, seq m k <= x
  have : WellFounded Nat.lt := by
    apply Nat.lt_wfRel.wf
  have well_ordering := @WellFounded.induction_bot ℕ Nat.lt this m 1 C
  unfold_let r C at well_ordering
  simp at well_ordering
  have seq_le_1 : ∃ k, seq m k <= 1 := by
    apply well_ordering
    {
      intro b hb x hx
      use (seq m x.succ)
      apply And.intro
      {
        have h0 : ∀ n, n = 0 ∨ n = 1 ∨ n > 1 := by
          intro n
          cases' n with n
          { simp }
          {
            cases' n with n
            { simp }
            { simp }
          }
        cases' h0 (seq m x) with h0 h1
        {
          have h1 := seq_pos hm h x
          rw [h0] at h1
          contradiction
        }
        {
          cases' h1 with h1 hg1
          {
            rw [seq_one_next h1]
            rw [h1] at hx
            exact Ne.lt_of_le' hb hx
          }
          {
            have hxs : seq m x.succ < seq m x := by
              apply seq_dec hm h hg1
            exact Nat.lt_of_lt_of_le hxs hx
          }
        }
      }
      use x.succ
    }
    {
      apply seq_lt_seq_zero hm h
    }
    exact 0
  have ⟨l, hl⟩ := seq_le_1
  have hseq_pos : seq m l > 0 := by apply seq_pos hm h
  use l
  exact Nat.le_antisymm hl hseq_pos

lemma iterate' {m x y : ℕ} (hmgt : m > 0) (hf : f x ≡ f y [MOD m]) (hm : 3^m ≡ 1 [MOD m]) :
  x ≡ y [MOD order m 3] -> x ≡ y [MOD m] := by
  intro hstep

  wlog hge : x >= y
  {
    have hyx : y >= x := Nat.le_of_not_le hge
    apply Nat.ModEq.symm at hf
    apply Nat.ModEq.symm at hstep
    apply Nat.ModEq.symm
    exact this hmgt hf hm hstep hyx
  }

  unfold f at hf

  let d := order m 3

  have hdgt : d > 0 := seq_pos hmgt hm 1
  have ⟨t, hdt⟩ : ∃ t, x = y + t * d := (Helper.add_fac_iff_mod hdgt hge).mp hstep
  have h3dm : 3^d ≡ 1 [MOD m] := seq_pow_mod_prev m 0
  have h3xym : 3^x ≡ 3^y [MOD m] := by
    rw [hdt, pow_add]
    have h0 : 3^y = 3^y * 1^t := by simp
    nth_rewrite 2 [h0]
    apply Nat.ModEq.mul_left
    rw [mul_comm, pow_mul]
    exact Nat.ModEq.pow t h3dm

  exact Nat.ModEq.add_left_cancel h3xym hf

lemma iterate {m x y k : ℕ} (hmgt : m > 0) (hf : f x ≡ f y [MOD m]) (hm : 3^m ≡ 1 [MOD m])
  (h : x ≡ y [MOD seq m k.succ]) : x ≡ y [MOD seq m k] := by
  have hsmk : 3^seq m k ≡ 1 [MOD seq m k] := seq_pow_one hm k
  have hpos : seq m k > 0 := seq_pos hmgt hm k
  have hdvd : seq m k ∣ m := seq_dvd_seq_zero hm k
  have hfsmk : f x ≡ f y [MOD seq m k] := by
    have ⟨d, hd⟩ := hdvd
    nth_rewrite 1 [hd] at hf
    exact Nat.ModEq.of_mul_right d hf
  exact iterate' hpos hfsmk hsmk h

theorem bijection_mod_m {m x y : ℕ} (hmgt : m > 0) (hf : f x ≡ f y [MOD m]) (hm : 3^m ≡ 1 [MOD m])
  : x ≡ y [MOD m] := by
  have hxy1 : x ≡ y [MOD 1] := Nat.modEq_one
  have ⟨idx, hidx⟩ := seq_one hmgt hm

  let r := Nat.lt
  let C := fun k => x ≡ y [MOD seq m k]
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
      exact iterate hmgt hf hm hcb
    }
  }
  {
    unfold_let
    simp
    rw [hidx]
    exact hxy1
  }
