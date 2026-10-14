import Hindman168.MaskColorFamilySelectedQuality
import Hindman168.MaskColorNativePredictionTransfer
import Hindman168.SelectedNativeMaskCorrelation

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

/-- Actual coloring dense models are chosen before the ultrafilter and
selected indices. The same family supplies every later rho-F replacement
and every selected native F-S estimate, preserving coarse representation,
projection accuracy and one common native manifold. The inverse
existence hypotheses remain explicit and unproved. -/
theorem selected_color_dense_native_models (ι : Type*) [Fintype ι]
    (r n m s : ℕ)
    (hinverse : ∀ d : ℕ, d ≤ maskRowCountBound m →
      HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ τ : ℝ, 0 < κ ∧ 0 < τ ∧ 2 * τ < κ ∧
      ∃ N : ℕ, ∀ (M : ℕ) (hM : 0 < M), N ≤ M →
      let gap₀ : ℕ → Fin M := fun _ => ⟨0, hM⟩
      let F := maskGeneratedMaster m gap₀
      ∀ (a : ι → ℚ) (_ha : ∀ γ, 0 < a γ)
        (χ : ℕ → Fin r) (color : ι → Fin r),
      ∃ f : Finset ℕ → (i : ℕ) → ι →
        boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)),
        (∀ T i γ w y, 0 ≤ (f T i γ).val w y ∧ (f T i γ).val w y ≤ 1) ∧
        (∀ T : Finset ℕ, ∀ i : Fin M, ∀ hT : T.Nonempty,
          ∀ hTi : T ⊆ Finset.range i.val, ∀ γ : ι,
          MaskColorBlockDualControl m (s+1) hM T i hT hTi (a γ) χ (color γ)
            (fun w y => (f T i.val γ).val w y)) ∧
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop),
      ∃ e : Fin (2 * n) ↪o ℕ, ∃ heM : ∀ j, e j < M,
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
          (∀ C : Chain (m+1), ∀ hC : ∀ i, C.block i ⊆ energyPrincipalSet e,
            ∃ p : Fin (m+1) → Fin n, StrictMono p ∧
              (∀ i, energyPrincipal e (p i) = C.pivot i) ∧
              (∀ i, ∀ y ∈ C.tail i, y < energyPadding e (p 0)) ∧
              let gap := masterGapIndex M hM (energyPadding e (p 0))
              let hCrange : ∀ col, C.block col ⊆ Finset.range M := fun col y hy => by
                obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC col hy)
                exact Finset.mem_range.mpr (heM _)
              (∀ γ : Fin (m+1) → ι, ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),
                maskModelReplacementQuality gap (fun col => a (γ col)) (fun _ => C)
                  (maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ
                    (fun col => color (γ col)))
                  (fun col w y => (f (C.tail col) (C.pivot col) (γ col)).val w y) η w) ∧
              (∀ (a : Fin (m+1) → ℚ) (_ha : ∀ col, 0 < a col)
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
              (∀ (γ : Fin (m+1) → ι)
                (H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ)
                (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ),
                (∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap (fun _ => C) w (H w) (b w)) →
                (∀ᶠ w in (U : Filter ℕ), ∀ V : NonemptyColumnSubset (m+1), 2 ≤ V.val.card →
                  H w V = maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ
                    (fun col => color (γ col)) (V.val.max' V.property) w) →
                ∀ᶠ w in (U : Filter ℕ),
                  |maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w (H w) (b w) -
                    maskOriginalSubsetCorrelation gap (fun col => a (γ col)) (fun _ => C) w
                      (maskSubsetModelReplacement (H w) (fun col y =>
                        (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w y)) (b w)| ≤
                    ((Fintype.card (LargeColumnSubset m) : ℝ) + 1) * ε)) ∧
          ∃ G : NativeNilmanifoldData.{u} s,
            letI := G.metric
            letI : TopologicalSpace (G.G ⧸ G.Γ) := G.metric.toUniformSpace.toTopologicalSpace
            ∃ B : ℝ, ∃ Lip : NNReal, 0 ≤ B ∧ ∀ T b a,
              ∃ (obs : ℕ → (ℤ × ℤ) → C(G.G ⧸ G.Γ, ℝ))
                (g x : ℕ → (ℤ × ℤ) → G.G),
                (∀ w p z, |obs w p z| ≤ B) ∧ (∀ w p, LipschitzWith Lip (obs w p)) ∧
                (fun w y => (model T b a).val w y) = piecewiseLinearNilsequence G.Γ F
                  (masterGapIndex M hM (energyPadding e b)) obs g x := by
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, hN⟩ :=
    selected_native_mask_original_correlations.{u} ι n m s hinverse ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd⟩ := mask_color_block_hilbert_family ι m (s+1) (by omega) hM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, hchains, hcommon⟩ := hN M hM hNM U hU f hf
  refine ⟨e, heM, model, hmodel, ?_, hcommon⟩
  intro C hC
  obtain ⟨p, hpmono, hp, hbefore, hFS⟩ := hchains C hC
  refine ⟨p, hpmono, hp, hbefore, ?_, hFS, ?_⟩
  · intro γ η hη
    exact hU (mask_color_family_selected_chain_quality ι m (s+1) hM a ha χ color f hf hd
      e heM C hC p hp γ η hη)
  · intro γ H b hH htarget
    let gap := masterGapIndex M hM (energyPadding e (p 0))
    have hCrange : ∀ col, C.block col ⊆ Finset.range M := by
      intro col y hy
      obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp (hC col hy)
      exact Finset.mem_range.mpr (heM _)
    exact mask_color_native_prediction_transfer gap (fun col => a (γ col)) (fun _ => C)
      (fun _ => hCrange) U hU
      (maskChainColorWeight m hM C hCrange (fun col => a (γ col)) χ (fun col => color (γ col)))
      (fun col w y => (f (C.tail col) (C.pivot col) (γ col)).val w y)
      (fun col w y => (model (principalTailPositions e (C.tail col)) (p col) (γ col)).val w y)
      (fun col => hf _ _ _) (fun col => (hmodel _ _ _).2.1) ε hε
      (hU (mask_color_family_selected_chain_quality ι m (s+1) hM a ha χ color f hf hd
        e heM C hC p hp γ ε hε))
      (fun z H b hH ht => hFS (fun col => a (γ col)) (fun col => ha (γ col)) z
        (γ (targetRootAnchor gap z)) H b hH ht) H b hH htarget

end Hindman168
