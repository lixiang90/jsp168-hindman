import Hindman168.PolynomialNormalizedIntegerRows
import Hindman168.NormalizedResponseResidueArithmetic

/-!
Exact integer responses of the paper's constructed translations.
These responses are units whenever the smooth factors and the specified
actual catalogue evaluations are units; no rational-to-residue map is used.
-/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

noncomputable def integerTranslationResponse
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i l : Fin r) : ℤ :=
  normalizedIntegerCoordinate (master.modulus w) (c (F.normalizationAnchor l))
    (c (F.normalizationAnchor target)) w
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l i))

noncomputable def rootIntegerTranslationResponse
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target l : Fin r) : ℤ :=
  normalizedRootIntegerCoordinate (master.modulus w) (c (F.normalizationAnchor l))
    (c (F.normalizationAnchor target))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l target))

theorem integerTranslationResponse_cast
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i l : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    (F.integerTranslationResponse master w c x target i l : ℚ) =
      F.normalizedLinearForm x c l (F.integerTranslation master w c x target i) := by
  rw [F.integerTranslation_response master w c x target i l hi hc habs hg]
  exact normalizedIntegerCoordinate_eq (primorial w) (master.modulus w)
    (c (F.normalizationAnchor l)) (c (F.normalizationAnchor target)) w (master.exponent w)
    _ _ _ (hc _) (hg.1.2 _ (F.denominator_mem_catalog target))
    (hg.1.2 _ (F.response_mem_catalog target target i hi.symm))
    (F.evaluated_response_dvd_denominator x target i hi) (habs _)
    (F.local_good_smooth_part_dvd target master w x hg)

theorem rootIntegerTranslationResponse_cast
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target l : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ)) :
    (F.rootIntegerTranslationResponse master w c x target l : ℚ) =
      F.normalizedLinearForm x c l (F.rootIntegerTranslation master w c x target) := by
  rw [F.rootIntegerTranslation_response master w c x target l hc habs]
  exact normalizedRootIntegerCoordinate_eq (master.modulus w)
    (c (F.normalizationAnchor l)) _ _ (hc _)
    ((dvd_mul_left _ ((primorial w) ^ (master.exponent w + 1))).trans (habs _))

theorem integerTranslationResponse_W_divisible
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i l : Fin r)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    (primorial w : ℤ) ∣ F.integerTranslationResponse master w c x target i l :=
  normalizedIntegerCoordinate_W_divisible (primorial w) (master.modulus w) _ _ w
    (master.exponent w) _ _ _ (habs _)
    (F.local_good_smooth_part_dvd target master w x hg)

theorem rootIntegerTranslationResponse_W_divisible
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target l : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ)) :
    (primorial w : ℤ) ∣ F.rootIntegerTranslationResponse master w c x target l :=
  normalizedRootIntegerCoordinate_W_divisible (primorial w) (master.modulus w) _ _
    (master.exponent w) _ (master.modulus w).pos (hc _) (habs _)

theorem integerTranslationResponse_residue_isUnit
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i l : Fin r) (hi : i ≠ target) (hl : l ≠ i)
    (q : ℕ)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x)
    (hM : IsUnit ((master.modulus w : ℕ) : ZMod q))
    (hcat : ∀ f ∈ F.catalog target,
      IsUnit ((MvPolynomial.eval (fun j => (x j : ℤ)) f : ℤ) : ZMod q)) :
    IsUnit (F.integerTranslationResponse master w c x target i l : ZMod q) := by
  have hcstar := natDivisor_residue_isUnit
    ((dvd_mul_left _ ((primorial w) ^ (master.exponent w + 1))).trans
      (habs (F.normalizationAnchor target))) hM
  exact normalizedIntegerCoordinate_residue_isUnit (primorial w) (master.modulus w)
    _ _ w (master.exponent w) q _ _ _ (hg.1.2 _ (F.denominator_mem_catalog target))
    (F.evaluated_response_dvd_denominator x target i hi) (habs _)
    (F.local_good_smooth_part_dvd target master w x hg) hM hcstar
    (hcat _ (F.denominator_mem_catalog target)) (hcat _ (F.response_mem_catalog target l i hl))

theorem rootIntegerTranslationResponse_residue_isUnit
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target l : Fin r) (hl : l ≠ target) (q : ℕ)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hM : IsUnit ((master.modulus w : ℕ) : ZMod q))
    (hcat : ∀ f ∈ F.catalog target,
      IsUnit ((MvPolynomial.eval (fun j => (x j : ℤ)) f : ℤ) : ZMod q)) :
    IsUnit (F.rootIntegerTranslationResponse master w c x target l : ZMod q) := by
  have hcstar := natDivisor_residue_isUnit
    ((dvd_mul_left _ ((primorial w) ^ (master.exponent w + 1))).trans
      (habs (F.normalizationAnchor target))) hM
  exact normalizedRootIntegerCoordinate_residue_isUnit (master.modulus w) _ _ q _
    ((dvd_mul_left _ ((primorial w) ^ (master.exponent w + 1))).trans (habs _))
    hM hcstar (hcat _ (F.response_mem_catalog target l target hl))

theorem normalizedIntegerLinearForm_translation_eq
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i l : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (hdiv : ∀ k, k ≤ F.normalizationAnchor l → c (F.normalizationAnchor l) ∣ c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.normalizedIntegerLinearForm x c l (F.integerTranslation master w c x target i) =
      F.integerTranslationResponse master w c x target i l := by
  have he := (F.normalizedIntegerLinearForm_cast x c l (hc _) hdiv
    (F.integerTranslation master w c x target i)).trans
    (F.integerTranslationResponse_cast master w c x target i l hi hc habs hg).symm
  exact_mod_cast he

theorem normalizedIntegerLinearForm_root_translation_eq
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target l : Fin r) (hc : ∀ k, 0 < c k)
    (hdiv : ∀ k, k ≤ F.normalizationAnchor l → c (F.normalizationAnchor l) ∣ c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ)) :
    F.normalizedIntegerLinearForm x c l (F.rootIntegerTranslation master w c x target) =
      F.rootIntegerTranslationResponse master w c x target l := by
  have he := (F.normalizedIntegerLinearForm_cast x c l (hc _) hdiv
    (F.rootIntegerTranslation master w c x target)).trans
    (F.rootIntegerTranslationResponse_cast master w c x target l hc habs).symm
  exact_mod_cast he

theorem integerTranslationResponse_responses
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.integerTranslationResponse master w c x target i target =
      (F.translationModulus master w x target : ℤ) ∧
    F.integerTranslationResponse master w c x target i i = 0 ∧
    ∀ l, l ≠ i → F.integerTranslationResponse master w c x target i l ≠ 0 := by
  have h := F.integerTranslation_responses master w c x target i hi hc habs hg
  refine ⟨?_, ?_, ?_⟩
  · have he := (F.integerTranslationResponse_cast master w c x target i target hi hc habs hg).trans h.1
    exact_mod_cast he
  · have he := (F.integerTranslationResponse_cast master w c x target i i hi hc habs hg).trans h.2.1
    exact_mod_cast he
  · intro l hl hz
    apply h.2.2 l hl
    rw [← F.integerTranslationResponse_cast master w c x target i l hi hc habs hg, hz, Int.cast_zero]

theorem rootIntegerTranslationResponse_responses
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.rootIntegerTranslationResponse master w c x target target = 0 ∧
    ∀ l, l ≠ target → F.rootIntegerTranslationResponse master w c x target l ≠ 0 := by
  have h := F.rootIntegerTranslation_responses master w c x target hc habs hg
  refine ⟨?_, ?_⟩
  · have he := (F.rootIntegerTranslationResponse_cast master w c x target target hc habs).trans h.1
    exact_mod_cast he
  · intro l hl hz
    apply h.2 l hl
    rw [← F.rootIntegerTranslationResponse_cast master w c x target l hc habs, hz, Int.cast_zero]

end Hindman168.PolynomialRowFamily
