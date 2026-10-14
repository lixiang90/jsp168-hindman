import Hindman168.MaskEndpointTerminalTransfer

/-! The actual repeated endpoint cube depends only on the tracked
function. The complete original additive output inequality is therefore
available for every target g, without a centered-target hypothesis. -/

set_option maxHeartbeats 2000000

namespace Hindman168
open Filter
open scoped Topology Classical
open FiniteMass MaskOriginalSampling

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m+1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m+1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ) (hJ : 0 < J)
  (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
  (htail : ∀ᶠ w in atTop, ∀ col, (C w).tail col ⊆ Finset.range (gap w).val)

noncomputable def maskEndpointTargetCube (w : ℕ) (g : ℤ → ℝ) : ℝ :=
  targetUnrestrictedAverage gap C t J (fun _ _ _ => g) w

theorem maskEndpointSource_targetCube_eq {w : ℕ} (D : MaskEndpointInput gap C t w)
    (g : ℤ → ℝ) (hD : maskRowStageInputHasTarget (maskSourceSupport m t) gap C D g) :
    targetUnrestrictedAverage gap C t J (fun _ => maskEndpointSource gap C t D) w =
      maskEndpointTargetCube gap C t J w g := by
  unfold maskEndpointTargetCube targetUnrestrictedAverage
  apply congrArg (expectation (rootPrimeMass gap t w))
  funext x
  apply congrArg (expectation (MaskRootOriginalSampling.directionPairMass gap t J w x))
  funext v
  apply congrArg (expectation (integerMass
    ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)))
  funext y
  unfold rootCubeTest
  apply Fintype.prod_congr
  intro η
  dsimp only
  rw [maskEndpointSource_root, hD x]

theorem maskEndpointFromTerminal_targetCube_eq {w : ℕ} (D : MaskIndexedTerminalInput gap C t w)
    (g : ℤ → ℝ) (hD : maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C D g) :
    targetUnrestrictedAverage gap C t J (fun _ => maskEndpointSource gap C t (maskEndpointFromTerminal gap C t D)) w =
      maskEndpointTargetCube gap C t J w g :=
  maskEndpointSource_targetCube_eq gap C t J _ g (maskEndpointFromTerminal_target gap C t D g hD)

include ha hC hJ hgap htail in
theorem maskTerminal_general_additive_output_uniform :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ w in atTop, ∀ g : ℤ → ℝ, ∀ E : MaskIndexedTerminalInput gap C t w,
      maskStageInputHasTarget (maskSourceSupport m t) (maskSourceSupport_card m t) gap C E g →
      |maskStageInputCorrelation (maskSourceSupport m t) (maskSourceSupport_card m t) gap a C E| ^
        (2 ^ targetPredictionOrder gap t) ≤
        maskAdditiveOutputBound m * |maskEndpointTargetCube gap C t J w g| + ε := by
  intro ε hε
  filter_upwards [source_raw_general_additive_output_uniform gap a ha C hC t J hJ hgap htail
    (maskEndpointLabel gap t) ε hε] with w hw
  intro g E hE
  have he := hw (maskEndpointSource gap C t (maskEndpointFromTerminal gap C t E))
    (maskEndpointSource_majorized gap C t _)
  rw [← maskEndpointFromTerminal_rawCorrelation gap a C t E,
    maskEndpointFromTerminal_targetCube_eq gap C t J E g hE] at he
  exact he

end Hindman168
