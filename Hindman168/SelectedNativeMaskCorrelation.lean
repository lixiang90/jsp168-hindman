import Hindman168.SelectedChainMaskShortCubeTransfer
import Hindman168.MaskRenamedShortCubeLaw
import Hindman168.FiniteOrderNativeChainPrediction

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

/-- One family of actual selected native models controls F-S in every
original subset correlation on every selected chain. The quotient scale,
accuracies and required master count are chosen first. The interval
inverse existence inputs remain explicit hypotheses. -/
theorem selected_native_mask_original_correlations (ι : Type*) [Fintype ι]
    (n m s : ℕ)
    (hinverse : ∀ d : ℕ, d ≤ maskRowCountBound m →
      HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ τ : ℝ, 0 < κ ∧ 0 < τ ∧ 2 * τ < κ ∧
      ∃ N : ℕ, ∀ (M : ℕ) (hM : 0 < M), N ≤ M →
      let gap₀ : ℕ → Fin M := fun _ => ⟨0, hM⟩
      let F := maskGeneratedMaster m gap₀
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (f : Finset ℕ → (i : ℕ) → ι →
          boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)))
        (_hf : ∀ T i a w y, 0 ≤ (f T i a).val w y ∧ (f T i a).val w y ≤ 1),
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < M) ∧
        ∃ model : (T : Finset (Fin n)) → (b : Fin n) → ι →
          boundedHilbertFamilies (fun w => FiniteMassL2
            (originalPivotMass F (energyPrincipal e b) w)),
          (∀ T b a,
            NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b))
              (fun w y => (model T b a).val w y) ∧
            (∀ w y, 0 ≤ (model T b a).val w y ∧ (model T b a).val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                (masterGapIndex M hM (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U
                  (f (T.image (energyPrincipal e)) (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U (model T b a)‖ < τ) ∧
          (∀ C : Chain (m+1), (∀ i, C.block i ⊆ energyPrincipalSet e) →
            ∃ p : Fin (m+1) → Fin n, StrictMono p ∧
              (∀ i, energyPrincipal e (p i) = C.pivot i) ∧
              (∀ i, ∀ y ∈ C.tail i, y < energyPadding e (p 0)) ∧
              let gap := masterGapIndex M hM (energyPadding e (p 0))
              ∀ (a : Fin (m+1) → ℚ) (_ha : ∀ col, 0 < a col)
                (z : Fin (Fintype.card (LargeColumnSubset m))) (γ : ι)
                (H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ)
                (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
                (_hH : ∀ᶠ w in (U : Filter ℕ),
                  maskOriginalSubsetAdmissible gap (fun _ => C) w (H w) (b w))
                (_htarget : ∀ᶠ w in (U : Filter ℕ),
                  H w (maskSourceNonemptySupport m z) = fun y =>
                    (f (C.tail (targetRootAnchor gap z)) (C.pivot (targetRootAnchor gap z)) γ).val w y -
                      (model (principalTailPositions e (C.tail (targetRootAnchor gap z)))
                        (p (targetRootAnchor gap z)) γ).val w y),
              ∀ᶠ w in (U : Filter ℕ),
                |maskOriginalSubsetCorrelation gap a (fun _ => C) w (H w) (b w)| ≤ ε) ∧
          ∃ G : NativeNilmanifoldData.{u} s,
            letI := G.metric
            letI : TopologicalSpace (G.G ⧸ G.Γ) := G.metric.toUniformSpace.toTopologicalSpace
            ∃ B : ℝ, ∃ Lip : NNReal, 0 ≤ B ∧ ∀ T b a,
              ∃ (obs : ℕ → (ℤ × ℤ) → C(G.G ⧸ G.Γ, ℝ))
                (g x : ℕ → (ℤ × ℤ) → G.G),
                (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
                (fun w y => (model T b a).val w y) = piecewiseLinearNilsequence G.Γ F
                  (masterGapIndex M hM (energyPadding e b)) obs g x := by
  classical
  let δ := maskUniformDetectionTolerance m ε / 2
  have hδ : 0 < δ := div_pos (maskUniformDetectionTolerance_pos m hε) (by norm_num)
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, hN⟩ := finite_order_native_chain_prediction.{u}
    ι n s (Fin (maskRowCountBound m + 1)) (fun q => q.val)
    (fun q => hinverse q.val (Nat.le_of_lt_succ q.isLt)) δ hδ
  refine ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F U hU f hf
  let D := originalRowMasterCatalog (maskGeneratedRowDataFamily m gap₀)
  let hD := originalRowMasterCatalog_nonzero (maskGeneratedRowDataFamily m gap₀)
  obtain ⟨e, heM, model, hmodel, hchain, hcommon⟩ :=
    hN M hM hNM (maskMasterArity m) D hD U hU f hf
  refine ⟨e, heM, model, hmodel, ?_, hcommon⟩
  intro C hC
  obtain ⟨p, hpmono, hp, hbefore, hs⟩ := hchain m C hC
  refine ⟨p, hpmono, hp, hbefore, ?_⟩
  exact selected_chain_mask_correlation_of_shortCube hM e heM C hC p hp U hU J hJ
    F rfl (fun T i γ w y => (f T i γ).val w y)
    (fun T b γ w y => (model T b γ).val w y) ε hε hs

end Hindman168
