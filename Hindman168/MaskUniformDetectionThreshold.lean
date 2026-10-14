import Hindman168.MaskOriginalCorrelationOutput

/-! A positive target-cube tolerance chosen before the master count N.
The actual powered subset-correlation estimate supplies the same tolerance
for every target support. No decay of an arbitrary target cube is asserted. -/

namespace Hindman168
open Filter
open scoped Topology Classical

noncomputable def maskUniformDetectionTolerance (m : ℕ) (ε : ℝ) : ℝ :=
  ((min ε 1) ^ (2 ^ ((allNonemptyColumnMasks m).length + maskRowCountBound m)) / 2) /
    (maskFullOutputCoefficient m + 1)

theorem maskUniformDetectionTolerance_pos (m : ℕ) {ε : ℝ} (hε : 0 < ε) :
    0 < maskUniformDetectionTolerance m ε := by
  have hK := maskFullOutputCoefficient_ge_one m
  have hmin : 0 < min ε 1 := lt_min hε zero_lt_one
  unfold maskUniformDetectionTolerance
  positivity

theorem maskUniformDetectionTolerance_le_target {m N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) {ε : ℝ} (hε : 0 < ε) :
    maskUniformDetectionTolerance m ε ≤ maskFullDetectionTolerance gap t ε := by
  have hK := maskFullOutputCoefficient_ge_one m
  have hmin : 0 ≤ min ε 1 := le_min hε.le zero_le_one
  have hp := pow_le_pow_of_le_one hmin (min_le_right ε (1 : ℝ))
    (maskFullCorrelationPower_le_bound gap t)
  have hεpow := pow_le_pow_left₀ hmin (min_le_left ε (1 : ℝ))
    (maskFullCorrelationPower gap t)
  unfold maskUniformDetectionTolerance maskFullDetectionTolerance
  exact div_le_div_of_nonneg_right
    (div_le_div_of_nonneg_right (hp.trans hεpow) (by norm_num)) (by linarith)

theorem maskOriginalSubset_detection_before_master {m N : ℕ}
    (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
    (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
    (J : ℕ) (hJ : 0 < J)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
      ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ,
      ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w f b →
      |maskEndpointTargetCube gap C t J w (f (maskSourceNonemptySupport m t))| ≤
        maskUniformDetectionTolerance m ε →
      |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  apply eventually_all.mpr
  intro t
  filter_upwards [maskOriginalSubset_detection_uniform gap a ha C hC t J hJ hgap htail hε]
    with w hw
  intro f b hf hcube
  exact hw f b hf (hcube.trans (maskUniformDetectionTolerance_le_target gap t hε))

/-- The witness depends only on m and epsilon; N, the master gaps,
chain, rational coefficients, quotient scale and test functions come later. -/
theorem maskOriginalSubset_uniform_detection_threshold (m : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ {N : ℕ}
      (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (_ha : ∀ col, 0 < a col)
      (C : ℕ → Chain (m+1)) (_hC : ∀ w col, (C w).block col ⊆ Finset.range N)
      (J : ℕ) (_hJ : 0 < J)
      (_hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
      (_htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val),
      ∀ᶠ w in atTop, ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
        ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ,
        ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
        maskOriginalSubsetAdmissible gap C w f b →
        |maskEndpointTargetCube gap C t J w (f (maskSourceNonemptySupport m t))| ≤ δ →
        |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  refine ⟨maskUniformDetectionTolerance m ε, maskUniformDetectionTolerance_pos m hε, ?_⟩
  intro N gap a ha C hC J hJ hgap htail
  exact maskOriginalSubset_detection_before_master gap a ha C hC J hJ hgap htail hε

end Hindman168
