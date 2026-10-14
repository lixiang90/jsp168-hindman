import Hindman168.MaskBlockAllGapDenseModels
import Hindman168.MaskModelOriginalCorrelation

/-! The dense model chosen at an individual block before selecting a chain
annihilates the actual rho-model subset correlation in every later chain
whose tracked block has this tail and pivot, at every permissible gap.
The construction retains the zero-prime tests for later native comparison. -/

namespace Hindman168
open Filter
open scoped Topology Classical
open FiniteMass MaskOriginalSampling

theorem maskBlock_dual_control_targetCube (m d₀ : ℕ)
    {N : ℕ} (hN : 0 < N) (T : Finset ℕ) (i : Fin N)
    (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (ρ model : ℕ → ℤ → ℝ) (hm : ∀ w y, 0 ≤ model w y ∧ model w y ≤ 1)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤
      masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y)
    (l : MaskValidBlockGap T i) (C : ℕ → Chain (m+1))
    (t : Fin (Fintype.card (LargeColumnSubset m)))
    (hpivot : ∀ w, (C w).pivot (targetRootAnchor (fun _ => l.val) t) = i.val)
    (J : ℕ) (_hJ : 0 < J)
    (hdual : ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
      ∀ u : OriginalSingleDualInput
        (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t.succ).arity
        (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t.succ).dimension,
      u.Admissible (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w →
      |expectation (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val)
        (primorial w)) (fun y => (ρ w y - model w y) *
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t.succ).dual
            (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) (fun _ => J) u w y)| < η) :
    Tendsto (fun w => maskEndpointTargetCube (fun _ => l.val) C t J w
      (fun y => ρ w y - model w y)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply tendsto_order.2
  constructor
  · intro c hc
    exact Eventually.of_forall (fun _ => hc.trans_le (abs_nonneg _))
  · intro η hη
    filter_upwards [hρ, hdual η hη] with w hr hw
    have hu := originalRepeatedDualInput_admissible
      (a := (maskGeneratedRowDataFamily m (fun _ => l.val) t).arity)
      (d := (maskGeneratedRowDataFamily m (fun _ => l.val) t).template.dimension)
      (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
      (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w
      (fun y => ρ w y - model w y) (fun y => model_error_abs_bound (hr y) (hm w y))
    have he := hw (maskTargetRepeatedDualInput (fun _ => l.val) t
      (fun y => ρ w y - model w y)) hu
    rw [maskEndpointTargetCube_eq_original_template_pairing, hpivot]
    exact he

theorem maskBlock_all_gap_original_correlations (m d₀ : ℕ) (hd₀ : 0 < d₀)
    {N : ℕ} (hN : 0 < N) (A : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)
    (T : Finset ℕ) (i : Fin N) (hT : T.Nonempty) (hTi : T ⊆ Finset.range i.val)
    (ρ : ℕ → ℤ → ℝ)
    (hρ : ∀ᶠ w in atTop, ∀ y, 0 ≤ ρ w y ∧ ρ w y ≤
      masterPredictionBlockMask (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
        (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w y) :
    ∃ model : ℕ → ℤ → ℝ, (∀ w y, 0 ≤ model w y ∧ model w y ≤ 1) ∧
      (∀ l : MaskValidBlockGap T i,
        ∀ t : Fin (Fintype.card (LargeColumnSubset m) + 1),
        ∀ J : ℕ, 1 ≤ J → ∀ η : ℝ, 0 < η → ∀ᶠ w in atTop,
        ∀ u : OriginalSingleDualInput
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).arity
          (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dimension,
        u.Admissible (maskGeneratedMaster m (fun _ => ⟨0, hN⟩))
          (fun _ => maskBlockChain T i.val hT hTi) (fun _ => 0) w →
        |expectation (integerMass ((maskGeneratedMaster m (fun _ => ⟨0, hN⟩)).cutoff w i.val)
          (primorial w)) (fun y => (ρ w y - model w y) *
            (maskGeneratedDualTemplates m (fun _ => l.val) d₀ (fun _ => l.val) t).dual
              (maskGeneratedMaster m (fun _ => ⟨0, hN⟩)) (fun _ => J) u w y)| < η) ∧
      ∀ l : MaskValidBlockGap T i, ∀ a : Fin (m+1) → ℚ, (∀ col, 0 < a col) →
        ∀ C : ℕ → Chain (m+1),
        (∀ w col, (C w).block col ⊆ Finset.range N) →
        (∀ᶠ w in atTop, ∀ col, l.val.val ≤ (C w).pivot col) →
        (∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range l.val.val) →
        ∀ t : Fin (Fintype.card (LargeColumnSubset m)),
        (∀ w, (C w).tail (targetRootAnchor (fun _ => l.val) t) = T) →
        (∀ w, (C w).pivot (targetRootAnchor (fun _ => l.val) t) = i.val) →
        ∀ J : ℕ, 0 < J → ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop,
        ∀ f : NonemptyColumnSubset (m+1) → ℤ → ℝ, ∀ b : Finset (Fin (m+1)) → ℤ → ℝ,
        maskOriginalSubsetAdmissible (fun _ => l.val) C w f b →
        f (maskSourceNonemptySupport m t) = (fun y => ρ w y - model w y) →
        |maskOriginalSubsetCorrelation (fun _ => l.val) a C w f b| ≤ ε := by
  obtain ⟨_, model, _, _, hm, _, hd⟩ := maskBlock_all_gap_dense_models m d₀ hd₀ hN A hA
    T i hT hTi ρ hρ (fun _ _ => True) (fun _ => Eventually.of_forall (fun _ => True.intro))
  refine ⟨model, hm, hd, ?_⟩
  intro l a ha C hC hgap htail t _ hpivot J hJ ε hε
  have hcube := maskBlock_dual_control_targetCube m d₀ hN T i hT hTi ρ model hm hρ
    l C t hpivot J hJ (hd l t.succ J (Nat.succ_le_iff.mpr hJ))
  exact maskTargetError_original_detection_uniform (fun _ => l.val) a ha C hC t J hJ hgap htail
    (fun w y => ρ w y - model w y) hcube hε

end Hindman168
