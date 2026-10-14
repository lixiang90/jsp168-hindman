import Hindman168.SmoothAbsorption

/-!
# A common smooth modulus absorbing all rational master coefficients

The extra numerator factor is necessary: integrality of H*a alone does
not imply that its resulting integer divides H. This file keeps that
factor and constructs one power of the actual primorial for the entire
finite coefficient family. The small-prime exponent e0 remains arbitrary.
-/

namespace Hindman168

open Filter
open scoped Topology

theorem rational_natural_den_identity (a : ℚ) (ha : 0 ≤ a) {H c : ℕ}
    (hc : (H : ℚ) * a = (c : ℚ)) : c * a.den = H * a.num.natAbs := by
  have hn : (a.num.natAbs : ℤ) = a.num := Int.natAbs_of_nonneg (Rat.num_nonneg.mpr ha)
  have hnr : (a.num.natAbs : ℚ) = (a.num : ℚ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) hn
  have he : (c : ℚ) * a.den = (H : ℚ) * a.num.natAbs := by
    rw [← hc, mul_assoc, Rat.mul_den_eq_num, hnr]
  exact_mod_cast he

theorem rational_natural_dvd_numerator (a : ℚ) (ha : 0 ≤ a) {H c : ℕ}
    (hc : (H : ℚ) * a = (c : ℚ)) : c ∣ H * a.num.natAbs := by
  rw [← rational_natural_den_identity a ha hc]
  exact dvd_mul_right _ _

def smoothMasterModulus (w N e0 : ℕ) : ℕ :=
  (primorial w) ^ ((e0 + 1) + (w * binaryWeight (Finset.range N) + w))

theorem smoothMasterModulus_pos (w N e0 : ℕ) : 0 < smoothMasterModulus w N e0 :=
  Nat.pow_pos (primorial_pos w)

theorem commonModulus_dvd_smoothMasterModulus (w N e0 : ℕ) :
    commonModulus (primorial w) w N ∣ smoothMasterModulus w N e0 :=
  pow_dvd_pow _ (by omega)

theorem power_dvd_smoothMasterModulus (w N e0 : ℕ) :
    (primorial w) ^ w ∣ smoothMasterModulus w N e0 :=
  pow_dvd_pow _ (by omega)

theorem masterScale_dvd_smoothMasterModulus {N : ℕ} {S : Finset ℕ} (w e0 : ℕ)
    (hS : S ⊆ Finset.range N) :
    masterScale (primorial w) w N S ∣ smoothMasterModulus w N e0 :=
  (masterScale_dvd_commonModulus _ _ hS).trans
    (commonModulus_dvd_smoothMasterModulus w N e0)

theorem rational_coefficient_dvd_smoothMasterModulus {N w e0 c : ℕ}
    {S : Finset ℕ} (a : ℚ) (ha : 0 < a) (hS : S ⊆ Finset.range N)
    (hw : a.num.natAbs ≤ w)
    (hc : (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ)) :
    (primorial w) ^ (e0 + 1) * c ∣ smoothMasterModulus w N e0 := by
  have hnum : a.num.natAbs ≠ 0 := by
    simpa using (Rat.num_pos.mpr ha).ne'
  have hC : c ∣ (primorial w) ^ (w * binaryWeight (Finset.range N) + w) := by
    have hmul := mul_dvd_mul (masterScale_dvd_commonModulus (primorial w) w hS)
      (fixed_integer_dvd_primorial_power hnum hw)
    have hd := (rational_natural_dvd_numerator a ha.le hc).trans hmul
    simpa only [commonModulus, ← pow_add] using hd
  simpa only [smoothMasterModulus, pow_add] using
    mul_dvd_mul_left ((primorial w) ^ (e0 + 1)) hC

theorem rational_smoothMasterModulus_absorbs {N w : ℕ} {S : Finset ℕ}
    (a : ℚ) (ha : 0 < a) (hS : S ⊆ Finset.range N) (hSn : S.Nonempty)
    (hd : a.den ≤ w) (hn : a.num.natAbs ≤ w) (e0 : ℕ) :
    ∃ c : ℕ, 0 < c ∧ (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) ∧
      (primorial w) ^ (e0 + 1) * c ∣ smoothMasterModulus w N e0 := by
  obtain ⟨c, hc⟩ := rational_mul_nat_natural a ha.le
    (fixed_integer_dvd_masterScale a.den_nz hd hSn)
  have hp : (0 : ℚ) < c := hc ▸ mul_pos (by
    exact_mod_cast Nat.pow_pos (primorial_pos w)) ha
  refine ⟨c, by exact_mod_cast hp, hc, ?_⟩
  exact rational_coefficient_dvd_smoothMasterModulus a ha hS hn hc

theorem rational_family_smoothMasterModulus_absorbs (A : Finset ℚ) (N : ℕ)
    (hA : ∀ a ∈ A, 0 < a) :
    ∀ᶠ w in atTop, ∀ a ∈ A, ∀ S : Finset ℕ, S ⊆ Finset.range N → S.Nonempty →
      ∀ e0 : ℕ, ∃ c : ℕ, 0 < c ∧
        (masterScale (primorial w) w N S : ℚ) * a = (c : ℚ) ∧
        (primorial w) ^ (e0 + 1) * c ∣ smoothMasterModulus w N e0 := by
  apply (eventually_all_finset A).mpr
  intro a ha
  filter_upwards [eventually_ge_atTop a.den, eventually_ge_atTop a.num.natAbs] with w hd hn
  intro S hS hSn e0
  exact rational_smoothMasterModulus_absorbs a (hA a ha) hS hSn hd hn e0

end Hindman168
