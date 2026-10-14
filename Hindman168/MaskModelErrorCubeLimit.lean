import Hindman168.MaskModelCubePairing

/-! The actual bounded models have vanishing repeated error cubes for all
mask-generated templates rooted at the modeled block, and every fixed
positive quotient scale. The same model and companion stage work for the
whole finite family. No cube-decay premise is assumed. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m+1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)

noncomputable def maskPredictionBlockRoot (k : Fin (m+1)) (w : ℕ) : Fin N :=
  ⟨(C w).pivot k, Finset.mem_range.mp (hC w k (by simp [Chain.block]))⟩

theorem maskGeneratedDualTemplates_succ (d₀ : ℕ) (gap₀ : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :
    maskGeneratedDualTemplates m gap d₀ gap₀ t.succ =
      (maskGeneratedRowDataFamily m gap t).template := rfl

include hC in
theorem maskGenerated_block_models_targetCubes
    (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a) (k : Fin (m+1))
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧
      ρ w y ≤ masterPredictionBlockMask (maskGeneratedMaster m gap) C (fun _ => k) w y)
    (P : ℕ → ℕ → Prop) (hP : ∀ q, ∀ᶠ w in atTop, P q w) :
    ∃ (stage : ℕ → ℕ) (model : ℕ → ℤ → ℝ), Tendsto stage atTop atTop ∧
      (∀ w, stage w ≤ w) ∧ (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ᶠ w in atTop, P (stage w) w) ∧
      ∀ t : Fin (Fintype.card (LargeColumnSubset m)), targetRootAnchor gap t = k →
        ∀ J : ℕ, 0 < J → Tendsto (fun w => maskEndpointTargetCube gap C t J w
          (fun y => ρ w y - model w y)) atTop (𝓝 0) := by
  have hroot : ∀ᶠ w in atTop, (gap w).val ≤ (maskPredictionBlockRoot C hC k w).val :=
    hgap.mono (fun w hw => hw k)
  have htailroot : ∀ᶠ w in atTop, Finset.range (gap w).val ⊆
      Finset.range (maskPredictionBlockRoot C hC k w).val :=
    hroot.mono (fun _ hw => Finset.range_mono hw)
  obtain ⟨stage, model, hs, hsw, hm, hPw, hdual⟩ :=
    maskGenerated_all_positive_scales_models m gap A hA 1 (max 1 (maskRowCountBound m))
      (by decide) (le_max_left _ _) (le_max_right _ _) gap C hC (fun _ => k)
      (fun w => Finset.range (gap w).val) (htail.mono (fun _ hw => hw k))
      (maskPredictionBlockRoot C hC k) htailroot
      (Eventually.of_forall (fun _ => Finset.Subset.refl _)) hroot
      (Eventually.of_forall (fun _ => Finset.Subset.refl _)) hroot ρ hρ P hP
  refine ⟨stage, model, hs, hsw, hm, hPw, ?_⟩
  intro t ht J hJ
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro ε hε
    filter_upwards [hρ, hdual t.succ J (Nat.succ_le_iff.mpr hJ) ε hε] with w hr hw
    have hu := maskTargetRepeatedDualInput_admissible gap C t (fun _ => k) w
      (fun y => ρ w y - model w y) (fun y => model_error_abs_bound (hr y) (hm w y))
    have he := hw (maskTargetRepeatedDualInput gap t (fun y => ρ w y - model w y)) hu
    rw [maskEndpointTargetCube_eq_original_template_pairing, ht]
    exact he

end Hindman168
