import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Init.Function

def f (k : ℕ) (x : ZMod (2 ^ k)) : ZMod (2 ^ k) := 3 ^ x.val + x
def g (x : ℕ) : ℕ := 3 ^ x + x

open Function

namespace Helper
  lemma zmod_iff_add_fac {a b c : ℤ} : a ≡ b [ZMOD c] ↔ ∃ t, a = b + t * c := by
    rw [Int.modEq_comm, Int.modEq_iff_add_fac]
    apply Iff.intro
    { intro ⟨t, h⟩; use t; rw [mul_comm]; exact h }
    { intro ⟨t, h⟩; use t; rw [mul_comm]; exact h }

  lemma add_fac_iff_mod {a b c : ℕ} (hc : c > 0) (hab : a >= b):
    a ≡ b [MOD c] ↔ ∃ t, a = b + t * c := by
    apply Iff.intro
    {
      intro hmod
      have hmodz := Int.coe_nat_modEq_iff.mpr hmod
      have ⟨tz, htz⟩ := Helper.zmod_iff_add_fac.mp hmodz
      have habz : (↑a : ℤ) >= ↑b := Int.ofNat_le.mpr hab
      have hcz : (↑c : ℤ) > 0 := Int.ofNat_pos.mpr hc
      have hmodz2 : ↑a - ↑b = tz * ↑c := sub_eq_of_eq_add' htz
      have tzc_ge : tz * ↑c >= 0 := by
        rw [← hmodz2]
        apply Int.sub_nonneg_of_le
        exact habz
      have tz_ge : tz >= 0 := by
        apply (zero_le_mul_right hcz).mp
        exact tzc_ge
      have ⟨t, tz_nat⟩ : ∃ t, (↑t : ℕ) = tz := CanLift.prf tz tz_ge

      use t
      rw [← tz_nat] at htz
      exact Int.ofNat_inj.mp htz
    }
    {
      intro ⟨t, ht⟩
      unfold Nat.ModEq
      rw [ht]
      simp
    }
end Helper

lemma double_pow_div (n : ℕ) : 3^2^n ≡ 1 [MOD 2^(n+1)] := by
  induction' n with n h
  { simp }
  {
    have hge : 3^2^n >= 1 := by apply Nat.one_le_pow'
    have hmod : 2^(n+1) > 0 := by apply Nat.pow_two_pos
    have hge2 : 3^2^(n+1) >= 1 := by apply Nat.one_le_pow'
    have hmod2 : 2^(n+2) > 0 := by apply Nat.pow_two_pos

    rw [Nat.succ_eq_add_one]
    apply (Helper.add_fac_iff_mod hmod2 hge2).mpr
    have ⟨t, ht⟩ := (Helper.add_fac_iff_mod hmod hge).mp h

    use t * (1 + t * 2^n)

    have ht2 : (3^2^n)^2 = (1 + t * 2^(n+1))^2 := by rw [ht];
    have h2 : (3^2^n)^2 = 3^2^(n+1) := by ring
    rw [← h2]
    rw [ht2]
    ring
  }

lemma one_mod_pow (a n : ℕ) (m : ℕ) : a ≡ 1 [MOD m] -> a^n ≡ 1 [MOD m] := by
  intro h
  rw [← Nat.one_pow n]
  apply Nat.ModEq.pow
  exact h

lemma div_pow_diff (k : ℕ) (x y : ℕ) :
  x ≡ y [MOD 2^k] -> 3^x ≡ 3^y [MOD 2^(k+1)] := by
  intro hxyk
  wlog hge : x >= y
  {
    have hyx : y >= x := Nat.le_of_not_le hge
    apply Nat.ModEq.symm
    apply this k
    { apply Nat.ModEq.symm hxyk }
    { exact hyx }
  }
  have h3ge : 3^x >= 3^y := by
    apply Nat.pow_le_pow_of_le_right
    { simp }
    { exact hge }
  have ⟨a, hxyk⟩ := (Helper.add_fac_iff_mod (Nat.pow_two_pos _) hge).mp hxyk
  apply (Helper.add_fac_iff_mod (Nat.pow_two_pos _) h3ge).mpr
  rw [hxyk]
  rw [pow_add]
  rw [mul_comm a]
  rw [pow_mul]
  have ht2n : (3^2^k)^a ≡ 1 [MOD 2^(k+1)] := by
    apply one_mod_pow
    apply double_pow_div

  have mod_pos := Nat.pow_two_pos (k+1)
  have pow_ge : (3^2^k)^a >= 1 := by
    apply Nat.one_le_pow
    apply Nat.one_le_pow'
  have ⟨t2, ht2n⟩ := (Helper.add_fac_iff_mod mod_pos pow_ge).mp ht2n

  rw [ht2n]
  use 3^y * t2
  ring

lemma inductive_step (k : ℕ) (x y : ℕ) (h : g x ≡ g y [MOD 2^k]) :
  ∀ m, m < k -> x ≡ y [MOD 2^m] -> x ≡ y [MOD 2^(m+1)] := by
  intro m hmk hxym

  wlog hge : x >= y
  {
    have hyx : y >= x := Nat.le_of_not_le hge
    apply Nat.ModEq.symm
    apply this k
    { apply Nat.ModEq.symm h }
    { exact hmk }
    { apply Nat.ModEq.symm hxym }
    exact hyx
  }
  have h3ge : 3^x >= 3^y := by
    apply Nat.pow_le_pow_of_le_right
    { simp }
    { exact hge }
  have hg_ge : 3^x+x >= 3^y+y := Nat.add_le_add h3ge hge

  unfold g at h

  have modk_pos : 2^k > 0 := Nat.pow_two_pos k
  have modm_pos : 2^m > 0 := Nat.pow_two_pos m
  have modm1_pos : 2^(m+1) > 0 := Nat.pow_two_pos (m+1)

  have ⟨a, h_mul⟩ := (Helper.add_fac_iff_mod modk_pos hg_ge).mp h
  have ⟨b, hxy_mul⟩ := (Helper.add_fac_iff_mod modm_pos hge).mp hxym
  have ⟨c, h3xy_mul⟩ : ∃ t, 3^x = 3^y + t * 2^(m+1) := by
    have h := (div_pow_diff _ _ _ hxym)
    exact (Helper.add_fac_iff_mod (Nat.pow_two_pos _) h3ge).mp h

  rw [h3xy_mul, hxy_mul] at h_mul
  have hsimp : c * 2^(m+1) + b * 2^m = a * 2^k := by linarith

  have ⟨d, hdvd_mk⟩ : 2^(m+1) ∣ 2^k := by
    apply pow_dvd_pow
    exact hmk

  rw [hdvd_mk, pow_add] at hsimp
  have hsimp2 : (2 * c + b) * 2^m = (2 * a * d) * 2^m := by linarith
  have hsimp3 : 2 * c + b = 2 * a * d := by
    apply Nat.eq_of_mul_eq_mul_right modm_pos
    exact hsimp2

  have dvd1 : 2 ∣ 2 * c := Nat.dvd_mul_right 2 _
  have dvd2 : 2 ∣ 2 * c + b := by
    rw [hsimp3, mul_assoc]
    apply Nat.dvd_mul_right

  have ⟨t2, hb⟩ := (Nat.dvd_add_right dvd1).mp dvd2
  apply (Helper.add_fac_iff_mod modm1_pos hge).mpr

  use t2

  rw [hb] at hxy_mul
  rw [pow_add]
  simp
  linarith

lemma inductive_step_conclusion (k : ℕ) (x y : ℕ) (h : g x ≡ g y [MOD 2^k]) :
  ∀ m : ℕ, m < k -> x ≡ y [MOD 2^m] := by
  intro m
  induction' m with m h1
  { intro _; apply Nat.modEq_one }
  {
    intro hm1k
    have hmk : m < k := Nat.le_of_lt hm1k
    have hmodm := h1 hmk
    exact inductive_step k x y h m hmk hmodm
  }

lemma inductive_step_final (k : ℕ) (x y : ℕ) (h : g x ≡ g y [MOD 2^k]) :
  x ≡ y [MOD 2^k] := by
  cases' k with n
  { simp; apply Nat.modEq_one }
  {
    have hmodn: x ≡ y [MOD 2^n] := by
      apply inductive_step_conclusion _ _ _ h
      simp
    apply inductive_step _ _ _ h
    simp
    exact hmodn
  }
