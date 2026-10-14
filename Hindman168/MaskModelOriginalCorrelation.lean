import Hindman168.MaskModelErrorCubeLimit
import Hindman168.MaskOriginalCorrelationOutput

/-! Actual bounded block models cancel the original subset correlation
whenever its tracked factor is their error. All other factors and product
masks remain arbitrary within the original admissibility bounds. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped Topology Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

include ha hC hJ hgap htail in
theorem maskTargetError_original_detection_uniform (e : ℕ → ℤ → ℝ)
    (hcube : Tendsto (fun w => maskEndpointTargetCube gap C t J w (e w)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ,
      ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
      maskOriginalSubsetAdmissible gap C w f b → f (maskSourceNonemptySupport m t) = e w →
      |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  have hδ := maskFullDetectionTolerance_pos gap t hε
  filter_upwards [maskOriginalSubset_detection_uniform gap a ha C hC t J hJ hgap htail hε,
    hcube.abs.eventually (eventually_lt_nhds (by simpa only [abs_zero] using hδ))] with w hw hcw
  intro f b hf htarget
  apply hw f b hf
  rw [htarget]
  exact hcw.le

include ha hC hgap htail in
theorem maskGenerated_block_models_originalCorrelations (k : Fin (m+1))
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => k) w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : Fin (Fintype.card (LargeColumnSubset m)), MaskOriginalSampling.targetRootAnchor gap t = k →
        ∀ J : ℕ, 0 < J → ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
          ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
          maskOriginalSubsetAdmissible gap C w f b →
          f (maskSourceNonemptySupport m t) = (fun y => ρ w y - model w y) →
          |maskOriginalSubsetCorrelation gap a C w f b| ≤ ε := by
  have hA : ∀ r ∈ (Finset.univ.image a), 0 < r := by
    intro r hr
    obtain ⟨col, _, rfl⟩ := Finset.mem_image.mp hr
    exact ha col
  obtain ⟨stage, model, hs, hsw, hm, hPw, hcube⟩ :=
    maskGenerated_block_models_targetCubes gap C hC (Finset.univ.image a) hA k hgap htail ρ hρ P hP
  refine ⟨stage, model, hs, hsw, hm, hPw, ?_⟩
  intro t ht J hJ ε hε
  exact maskTargetError_original_detection_uniform gap a ha C hC t J hJ hgap htail
    (fun w y => ρ w y - model w y) (hcube t ht J hJ) hε

include ha hC hJ hgap htail in
theorem maskTargetError_originalCorrelation_tendsto_zero (e : ℕ → ℤ → ℝ)
    (hcube : Tendsto (fun w => maskEndpointTargetCube gap C t J w (e w)) atTop (𝓝 0))
    (f : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ) (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
    (hf : ∀ᶠ w in atTop, maskOriginalSubsetAdmissible gap C w (f w) (b w))
    (htarget : ∀ᶠ w in atTop, f w (maskSourceNonemptySupport m t) = e w) :
    Tendsto (fun w => maskOriginalSubsetCorrelation gap a C w (f w) (b w)) atTop (𝓝 0) := by
  apply maskOriginalSubset_tendsto_zero_of_targetCube gap a ha C hC t J hJ hgap htail f b hf
  apply hcube.congr'
  filter_upwards [htarget] with w hw
  rw [hw]

end Hindman168
