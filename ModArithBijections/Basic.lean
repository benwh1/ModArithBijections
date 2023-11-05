import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Parity
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Defs
import Mathlib.Init.Function

def f (x : ℕ) : ℕ := 3 ^ x + x

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
