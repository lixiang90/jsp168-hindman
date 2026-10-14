import Hindman168.MasterColumnCoefficients

/-!
# Constructed integer translations and their exact normalized responses

The directions and denominator are the previously constructed actual
polynomial data. The rational expressions are proved equal to explicitly
cleared integer coordinates. Maximum-support anchors normalize the rows.
-/

namespace Hindman168.PolynomialRowFamily

open scoped BigOperators Classical

variable {n r m : ℕ}

noncomputable def integerTranslation
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i : Fin r) : Fin (m + 1) → ℤ := fun k =>
  normalizedIntegerCoordinate (master.modulus w) (c k) (c (F.normalizationAnchor target)) w
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction i k))

noncomputable def rootIntegerTranslation
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) : Fin (m + 1) → ℤ := fun k =>
  normalizedRootIntegerCoordinate (master.modulus w) (c k) (c (F.normalizationAnchor target))
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction target k))

noncomputable def translationModulus
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (x : Fin n → ℕ) (target : Fin r) : ℕ :=
  (master.modulus w : ℕ) * roughPartNat w
    (MvPolynomial.eval (fun j => (x j : ℤ)) (F.denominator target)).natAbs

theorem integerTranslation_formula
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x)
    (k : Fin (m + 1)) :
    (F.integerTranslation master w c x target i k : ℚ) =
      (F.translationModulus master w x target : ℚ) *
        ((c (F.normalizationAnchor target) : ℚ) / c k) *
        ((MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction i k) : ℚ) /
          MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i)) := by
  exact normalizedIntegerCoordinate_eq (primorial w) (master.modulus w) (c k)
    (c (F.normalizationAnchor target)) w (master.exponent w) _ _ _ (hc k)
    (hg.1.2 _ (F.denominator_mem_catalog target))
    (hg.1.2 _ (F.response_mem_catalog target target i hi.symm))
    (F.evaluated_response_dvd_denominator x target i hi) (habs k)
    (F.local_good_smooth_part_dvd target master w x hg)

theorem integerTranslation_W_divisible
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i : Fin r)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x)
    (k : Fin (m + 1)) :
    (primorial w : ℤ) ∣ F.integerTranslation master w c x target i k :=
  normalizedIntegerCoordinate_W_divisible (primorial w) (master.modulus w) (c k)
    (c (F.normalizationAnchor target)) w (master.exponent w) _ _ _ (habs k)
    (F.local_good_smooth_part_dvd target master w x hg)

theorem rootIntegerTranslation_W_divisible
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (k : Fin (m + 1)) :
    (primorial w : ℤ) ∣ F.rootIntegerTranslation master w c x target k :=
  normalizedRootIntegerCoordinate_W_divisible (primorial w) (master.modulus w) (c k)
    (c (F.normalizationAnchor target)) (master.exponent w) _ (master.modulus w).pos
    (hc k) (habs k)

theorem normalizedLinearForm_scaled
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (x : Fin n → ℕ) (c : Fin (m + 1) → ℕ) (hc : ∀ k, 0 < c k)
    (l : Fin r) (cstar : ℕ) (B : ℚ) (v z : Fin (m + 1) → ℤ)
    (hv : ∀ k, (v k : ℚ) = B * ((cstar : ℚ) / c k) * (z k : ℚ)) :
    F.normalizedLinearForm x c l v = B * ((cstar : ℚ) / c (F.normalizationAnchor l)) *
      (∑ k, (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row l k) : ℚ) * (z k : ℚ)) := by
  have hca : (c (F.normalizationAnchor l) : ℚ) ≠ 0 := by exact_mod_cast (hc _).ne'
  unfold normalizedLinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  have hck : (c k : ℚ) ≠ 0 := by exact_mod_cast (hc k).ne'
  rw [hv k]
  field_simp

theorem integerTranslation_response
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i l : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.normalizedLinearForm x c l (F.integerTranslation master w c x target i) =
      (F.translationModulus master w x target : ℚ) *
        ((c (F.normalizationAnchor target) : ℚ) / c (F.normalizationAnchor l)) *
        ((MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l i) : ℚ) /
          MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i)) := by
  have hv := F.normalizedLinearForm_scaled x c hc l (c (F.normalizationAnchor target))
    ((F.translationModulus master w x target : ℚ) /
      MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i))
    (F.integerTranslation master w c x target i)
    (fun k => MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction i k))
    (fun k => (F.integerTranslation_formula master w c x target i hi hc habs hg k).trans (by ring))
  have he : (∑ k, (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row l k) : ℚ) *
      (MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction i k) : ℚ)) =
      (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l i) : ℚ) := by
    exact_mod_cast F.evaluated_direction_response x l i
  rw [he] at hv
  exact hv.trans (by ring)

theorem rootIntegerTranslation_response
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target l : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ)) :
    F.normalizedLinearForm x c l (F.rootIntegerTranslation master w c x target) =
      (master.modulus w : ℚ) *
        ((c (F.normalizationAnchor target) : ℚ) / c (F.normalizationAnchor l)) *
        (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l target) : ℚ) := by
  have hv := F.normalizedLinearForm_scaled x c hc l (c (F.normalizationAnchor target))
    (master.modulus w : ℚ) (F.rootIntegerTranslation master w c x target)
    (fun k => MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction target k)) (fun k =>
      normalizedRootIntegerCoordinate_eq (master.modulus w) (c k) _ _ (hc k)
        ((dvd_mul_left (c k) ((primorial w) ^ (master.exponent w + 1))).trans (habs k)))
  have he : (∑ k, (MvPolynomial.eval (fun j => (x j : ℤ)) (F.row l k) : ℚ) *
      (MvPolynomial.eval (fun j => (x j : ℤ)) (F.direction target k) : ℚ)) =
      (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l target) : ℚ) := by
    exact_mod_cast F.evaluated_direction_response x l target
  simpa only [he] using hv

theorem translationModulus_pos
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (x : Fin n → ℕ) (target : Fin r)
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    0 < F.translationModulus master w x target :=
  Nat.mul_pos (master.modulus w).pos (roughPartNat_pos
    (Int.natAbs_ne_zero.mpr (hg.1.2 _ (F.denominator_mem_catalog target))))

theorem integerTranslation_responses
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target i : Fin r) (hi : i ≠ target)
    (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.normalizedLinearForm x c target (F.integerTranslation master w c x target i) =
      (F.translationModulus master w x target : ℚ) ∧
    F.normalizedLinearForm x c i (F.integerTranslation master w c x target i) = 0 ∧
      ∀ l, l ≠ i → F.normalizedLinearForm x c l (F.integerTranslation master w c x target i) ≠ 0 := by
  have hd : (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response target i) : ℚ) ≠ 0 := by
    exact_mod_cast hg.1.2 _ (F.response_mem_catalog target target i hi.symm)
  have hct : (c (F.normalizationAnchor target) : ℚ) ≠ 0 := by exact_mod_cast (hc _).ne'
  refine ⟨?_, ?_, ?_⟩
  · rw [F.integerTranslation_response master w c x target i target hi hc habs hg]
    simp only [div_self hct, div_self hd, mul_one]
  · rw [F.integerTranslation_response master w c x target i i hi hc habs hg,
      F.response_self, map_zero, Int.cast_zero, zero_div, mul_zero]
  · intro l hl
    rw [F.integerTranslation_response master w c x target i l hi hc habs hg]
    have hcl : (c (F.normalizationAnchor l) : ℚ) ≠ 0 := by exact_mod_cast (hc _).ne'
    have hr : (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l i) : ℚ) ≠ 0 := by
      exact_mod_cast hg.1.2 _ (F.response_mem_catalog target l i hl)
    have hM : (F.translationModulus master w x target : ℚ) ≠ 0 := by
      exact_mod_cast (F.translationModulus_pos master w x target hg).ne'
    exact mul_ne_zero (mul_ne_zero hM (div_ne_zero hct hcl)) (div_ne_zero hr hd)

theorem rootIntegerTranslation_responses
    (F : PolynomialRowFamily (MvPolynomial (Fin n) ℤ) r m)
    (master : MasterParameterFamily) (w : ℕ) (c : Fin (m + 1) → ℕ)
    (x : Fin n → ℕ) (target : Fin r) (hc : ∀ k, 0 < c k)
    (habs : ∀ k, (primorial w) ^ (master.exponent w + 1) * c k ∣ (master.modulus w : ℕ))
    (hg : predictionLocalPrimeGoodEvent master (F.catalog target) (F.denominator target) w x) :
    F.normalizedLinearForm x c target (F.rootIntegerTranslation master w c x target) = 0 ∧
      ∀ l, l ≠ target → F.normalizedLinearForm x c l (F.rootIntegerTranslation master w c x target) ≠ 0 := by
  refine ⟨?_, ?_⟩
  · rw [F.rootIntegerTranslation_response master w c x target target hc habs,
      F.response_self, map_zero, Int.cast_zero, mul_zero]
  · intro l hl
    rw [F.rootIntegerTranslation_response master w c x target l hc habs]
    have hct : (c (F.normalizationAnchor target) : ℚ) ≠ 0 := by exact_mod_cast (hc _).ne'
    have hcl : (c (F.normalizationAnchor l) : ℚ) ≠ 0 := by exact_mod_cast (hc _).ne'
    have hr : (MvPolynomial.eval (fun j => (x j : ℤ)) (F.response l target) : ℚ) ≠ 0 := by
      exact_mod_cast hg.1.2 _ (F.response_mem_catalog target l target hl)
    have hM : (master.modulus w : ℚ) ≠ 0 := by exact_mod_cast (master.modulus w).pos.ne'
    exact mul_ne_zero (mul_ne_zero hM (div_ne_zero hct hcl)) hr

end Hindman168.PolynomialRowFamily
