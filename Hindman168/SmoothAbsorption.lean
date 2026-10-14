import Hindman168.MasterScales
import Mathlib.NumberTheory.Primorial
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Rat.Lemmas
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.FieldSimp

/-!
# Fixed denominators absorbed by the actual small-prime modulus

Here W is exactly primorial(w). Every fixed positive integer divides
W^w once w is at least that integer. Hence every nonempty subset scale
absorbs a fixed rational denominator, making its rational multiple an
integer. This is the integrality part of the master scales lemma.
-/

namespace Hindman168

open Filter
open scoped Topology

theorem fixed_integer_dvd_primorial_pow_self {n w : ℕ} (hn : n ≠ 0) (hw : n ≤ w) :
    n ∣ (primorial w) ^ n := by
  apply (Nat.dvd_pow_self_iff hn (primorial_ne_zero w)).mpr
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  exact hpp.mem_primeFactors
    (hpp.dvd_primorial_iff.mpr ((Nat.le_of_mem_primeFactors hp).trans hw))
    (primorial_ne_zero w)

theorem fixed_integer_dvd_primorial_power {n w : ℕ} (hn : n ≠ 0) (hw : n ≤ w) :
    n ∣ (primorial w) ^ w :=
  (fixed_integer_dvd_primorial_pow_self hn hw).trans (pow_dvd_pow _ hw)

theorem fixed_integer_eventually_dvd_primorial_power {n : ℕ} (hn : n ≠ 0) :
    ∀ᶠ w in atTop, n ∣ (primorial w) ^ w :=
  (eventually_ge_atTop n).mono (fun _ hw => fixed_integer_dvd_primorial_power hn hw)

theorem fixed_integer_dvd_masterScale {N w : ℕ} {S : Finset ℕ} {n : ℕ}
    (hn : n ≠ 0) (hw : n ≤ w) (hS : S.Nonempty) :
    n ∣ masterScale (primorial w) w N S :=
  (fixed_integer_dvd_primorial_power hn hw).trans (power_dvd_masterScale _ _ hS)

theorem rational_mul_nat_integral (a : ℚ) {H : ℕ} (hH : a.den ∣ H) :
    ∃ c : ℤ, (H : ℚ) * a = (c : ℚ) := by
  obtain ⟨d, rfl⟩ := hH
  refine ⟨(d : ℤ) * a.num, ?_⟩
  rw [Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  have ha : a = (a.num : ℚ) / a.den := (Rat.num_div_den a).symm
  conv_lhs => arg 2; rw [ha]
  have hd : (a.den : ℚ) ≠ 0 := by exact_mod_cast a.den_nz
  field_simp

theorem rational_masterScale_integral {N w : ℕ} {S : Finset ℕ} (a : ℚ)
    (hw : a.den ≤ w) (hS : S.Nonempty) :
    ∃ c : ℤ, (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) :=
  rational_mul_nat_integral a (fixed_integer_dvd_masterScale a.den_nz hw hS)

theorem rational_masterScale_eventually_integral {N : ℕ} {S : Finset ℕ} (a : ℚ)
    (hS : S.Nonempty) :
    ∀ᶠ w in atTop, ∃ c : ℤ, (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) :=
  (eventually_ge_atTop a.den).mono (fun _ hw => rational_masterScale_integral a hw hS)

theorem rational_mul_nat_natural (a : ℚ) (ha : 0 ≤ a) {H : ℕ} (hH : a.den ∣ H) :
    ∃ c : ℕ, (H : ℚ) * a = (c : ℚ) := by
  obtain ⟨c, hc⟩ := rational_mul_nat_integral a hH
  have hc0 : (0 : ℚ) ≤ c := hc ▸ mul_nonneg (Nat.cast_nonneg H) ha
  have hcZ : (0 : ℤ) ≤ c := by exact_mod_cast hc0
  refine ⟨c.toNat, hc.trans ?_⟩
  exact_mod_cast Int.eq_natCast_toNat.mpr hcZ

theorem rational_scale_ratio_integral (a b : ℚ) (ha : 0 ≤ a) (hb : 0 < b)
    {H_A H_B w : ℕ} (hHB : 0 < H_B)
    (hdiv : H_B * (primorial w) ^ w ∣ H_A) (hw : (a / b).den + 1 ≤ w) :
    ∃ c : ℕ, ((H_A : ℚ) * a) / ((H_B : ℚ) * b) = (primorial w : ℚ) * c := by
  obtain ⟨d, hd⟩ := hdiv
  have he : w = (w - 1) + 1 := by omega
  have hden : (a / b).den ∣ (primorial w) ^ (w - 1) :=
    (fixed_integer_dvd_primorial_pow_self (a / b).den_nz (by omega)).trans
      (pow_dvd_pow _ (by omega : (a / b).den ≤ w - 1))
  obtain ⟨c, hc⟩ := rational_mul_nat_natural (a / b) (div_nonneg ha hb.le)
    (hden.trans (dvd_mul_right _ d))
  refine ⟨c, ?_⟩
  have hHBr : (H_B : ℚ) ≠ 0 := by exact_mod_cast hHB.ne'
  have hpow : (primorial w) ^ w = (primorial w) ^ (w - 1) * primorial w := by
    calc
      _ = (primorial w) ^ ((w - 1) + 1) := congrArg (fun n => (primorial w) ^ n) he
      _ = _ := pow_succ _ _
  calc
    _ = (primorial w : ℚ) * (((primorial w) ^ (w - 1) * d : ℕ) : ℚ) * (a / b) := by
      rw [hd, hpow]
      push_cast
      field_simp
    _ = (primorial w : ℚ) * c := by rw [mul_assoc, hc]

theorem rational_chain_scale_ratio_integral {m N w : ℕ} (C : Chain m)
    (hC : ∀ i, C.block i ⊆ Finset.range N) (i j : Fin m) (hij : i < j)
    (a b : ℚ) (ha : 0 ≤ a) (hb : 0 < b) (hw : (a / b).den + 1 ≤ w) :
    ∃ c : ℕ,
      ((masterScale (primorial w) w N (C.block i) : ℚ) * a) /
        ((masterScale (primorial w) w N (C.block j) : ℚ) * b) = (primorial w : ℚ) * c :=
  rational_scale_ratio_integral a b ha hb (Nat.pow_pos (primorial_pos w))
    (chain_scale_divisibility C (primorial w) w hC i j hij) hw

theorem rational_family_masterScale_eventually_integral (A : Finset ℚ) (N : ℕ) :
    ∀ᶠ w in atTop, ∀ a ∈ A, ∀ S : Finset ℕ, S.Nonempty →
      ∃ c : ℤ, (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) := by
  apply (eventually_all_finset A).mpr
  intro a _
  exact (eventually_ge_atTop a.den).mono (fun _ hw S hS => rational_masterScale_integral a hw hS)

end Hindman168
