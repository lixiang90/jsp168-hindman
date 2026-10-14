import Hindman168.FiniteRestrictedDistance
import Hindman168.SamplingAsymptotics

/-! Affine harmonic root comparison with the original progression density.
The comparison is not normalized. A polynomial scalar loss on translation
is harmless at the paper's rapidly separated master scales. -/

namespace Hindman168

open scoped BigOperators Classical
open FiniteMass

noncomputable def integerProgressionMass (X W k : ℕ) (h : ℤ) : Mass ℤ :=
  (k : ℝ) • restrictedMass (integerMass X W) (fun y => (k : ℤ) ∣ y - h)

theorem integerProgressionMass_apply (X W k : ℕ) (h y : ℤ) :
    integerProgressionMass X W k h y =
      if (k : ℤ) ∣ y - h then (k : ℝ) * integerMass X W y else 0 := by
  simp only [integerProgressionMass, Finsupp.smul_apply, smul_eq_mul, restrictedMass_apply,
    mul_ite, mul_zero]

theorem integerEtaMass_eq_progression_zero (X W k : ℕ) :
    integerEtaMass X W k = integerProgressionMass X W k 0 := by
  ext y
  simp only [integerEtaMass_apply, integerProgressionMass_apply, sub_zero]

theorem integer_translation_apply (μ : Mass ℤ) (h y : ℤ) :
    μ.mapDomain (fun z => z + h) y = μ (y - h) := by
  have hi : Function.Injective (fun z : ℤ => z + h) := fun _ _ he => add_right_cancel he
  have he := Finsupp.mapDomain_apply hi μ (y - h)
  simpa only [sub_add_cancel] using he

theorem translatedEtaMass_eq_scaled_restricted (X W k : ℕ) (h : ℤ) :
    (integerEtaMass X W k).mapDomain (fun y => y + h) =
      (k : ℝ) • restrictedMass ((integerMass X W).mapDomain (fun y => y + h))
        (fun y => (k : ℤ) ∣ y - h) := by
  ext y
  rw [integer_translation_apply, integerEtaMass_apply]
  simp only [Finsupp.smul_apply, smul_eq_mul, restrictedMass_apply, integer_translation_apply,
    mul_ite, mul_zero]

noncomputable def affineRootError (X W k H : ℕ) : ℝ :=
  dilationError X W k + (k : ℝ) * translationError X W H

theorem integer_harmonic_affine_root_error {X W k : ℕ} {h : ℤ}
    (hX : 2 ≤ X) (hW : 0 < W) (hk : 0 < k) (hkX : k ≤ X)
    (hco : W.Coprime k) (hlog : (W : ℝ) / X < Real.log X) (hWh : (W : ℤ) ∣ h) :
    distance ((integerMass X W).mapDomain (fun z => (k : ℤ) * z + h))
      (integerProgressionMass X W k h) ≤ affineRootError X W k h.natAbs := by
  have hi : Function.Injective (fun z : ℤ => z + h) := fun _ _ he => add_right_cancel he
  have ht : distance ((integerMass X W).mapDomain (fun z => z + h)) (integerMass X W) ≤
      translationError X W h.natAbs := by
    have he := (integer_harmonic_translation_error hX hW hlog hWh).trans (min_le_right _ _)
    simpa only [translationError, Nat.cast_natAbs, Int.cast_abs] using he
  have hc : ((integerMass X W).mapDomain (fun z => (k : ℤ) * z)).mapDomain (fun z => z + h) =
      (integerMass X W).mapDomain (fun z => (k : ℤ) * z + h) := by
    rw [← Finsupp.mapDomain_comp]
    rfl
  calc
    _ ≤ distance ((integerMass X W).mapDomain (fun z => (k : ℤ) * z + h))
        ((integerEtaMass X W k).mapDomain (fun z => z + h)) +
      distance ((integerEtaMass X W k).mapDomain (fun z => z + h))
        (integerProgressionMass X W k h) := distance_triangle _ _ _
    _ ≤ dilationError X W k + (k : ℝ) * translationError X W h.natAbs := by
      apply add_le_add
      · rw [← hc, distance_push_injective hi]
        exact integer_harmonic_dilation_error hX hW hk hkX hco hlog
      · rw [translatedEtaMass_eq_scaled_restricted, integerProgressionMass]
        exact (distance_scaled_restricted_le _ _ _ (k : ℝ) (Nat.cast_nonneg k)).trans
          (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg k))
    _ = _ := rfl

theorem integer_harmonic_affine_expectation_error {X W k : ℕ} {h : ℤ}
    (hX : 2 ≤ X) (hW : 0 < W) (hk : 0 < k) (hkX : k ≤ X)
    (hco : W.Coprime k) (hlog : (W : ℝ) / X < Real.log X) (hWh : (W : ℤ) ∣ h)
    (f : ℤ → ℝ) (B : ℝ) (hB : 0 ≤ B) (hf : ∀ y, |f y| ≤ B) :
    |expectation (integerMass X W) (fun z => f ((k : ℤ) * z + h)) -
      expectation (integerProgressionMass X W k h) f| ≤ B * affineRootError X W k h.natAbs := by
  rw [← expectation_push]
  exact (expectation_difference_bound _ _ f B hf).trans
    (mul_le_mul_of_nonneg_left (integer_harmonic_affine_root_error hX hW hk hkX hco hlog hWh) hB)

end Hindman168
