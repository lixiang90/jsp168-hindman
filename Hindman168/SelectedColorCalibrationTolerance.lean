import Hindman168.SelectedColorCalibratedModelsCapped

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped BigOperators Topology Classical
universe u

/-- The requested calibration tolerance is fixed before the master count.
The same selected models have product calibration below 3*threshold + cap,
with no residual approximation term in that bound. Inverse existence
remains an explicit hypothesis. -/
theorem selected_color_calibration_tolerance (ι : Type*) [Fintype ι]
    (r n m s : ℕ)
    (hinverse : ∀ d : ℕ, d ≤ maskRowCountBound m →
      HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (cap : ℝ) (hcap : 0 < cap)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ τ : ℝ, 0 < κ ∧ 0 < τ ∧ τ < cap ∧ 2 * τ < κ ∧
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
          (∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
            ∀ hT : (T.image (energyPrincipal e)).Nonempty,
            ∀ hbefore : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b,
            ∀ v : ℕ → ℤ → ℝ,
              NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b)) v →
              (∀ w y, |v w y| ≤ 1) → ∀ η : ℝ, 0 < η → ∀ᶠ w in (U : Filter ℕ),
              |expectation (originalPivotMass F (energyPrincipal e b) w)
                (fun y => (maskBlockColorWeight m hM (T.image (energyPrincipal e))
                  ⟨energyPrincipal e b, heM _⟩ hT
                  (fun y hy => Finset.mem_range.mpr (hbefore y hy))
                  (a γ) χ (color γ) w y - (model T b γ).val w y) * v w y)| < τ + η) ∧
          (∀ (T : Finset (Fin n)) (b : Fin n) (γ : ι),
            ∀ hT : (T.image (energyPrincipal e)).Nonempty,
            ∀ hbefore : ∀ y ∈ T.image (energyPrincipal e), y < energyPrincipal e b,
            ∀ θ : ℝ, 0 < θ → ∀ᶠ w in (U : Filter ℕ),
              event (originalBlockProductMass F (T.image (energyPrincipal e)) (energyPrincipal e b)
                hT (fun y hy => Finset.mem_range.mpr (hbefore y hy)) w)
                (fun y => 0 < y ∧ χ (masterColumnCoefficient M (fun _ : Fin 1 => a γ)
                  (fun _ _ => insert (energyPrincipal e b) (T.image (energyPrincipal e))) w 0 * y.toNat) = color γ ∧
                  (model T b γ).val w y ≤ 2*θ) < 3*θ + cap) ∧
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
  obtain ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, hN⟩ :=
    selected_color_calibrated_models_capped.{u} ι r n m s hinverse cap hcap ε hε
  refine ⟨J, hJ, κ, τ, hκ, hτ, hcap_error, hsmall, N, ?_⟩
  intro M hM hNM gap₀ F a ha χ color
  obtain ⟨f, hf, hd, hselected⟩ := hN M hM hNM a ha χ color
  refine ⟨f, hf, hd, ?_⟩
  intro U hU
  obtain ⟨e, heM, model, hmodel, htest, hcal, hchains, hcommon⟩ := hselected U hU
  refine ⟨e, heM, model, hmodel, htest, ?_, hchains, hcommon⟩
  intro T b γ hT hbefore θ hθ
  have ht := hcal T b γ hT hbefore θ hθ (cap-τ) (sub_pos.mpr hcap_error)
  filter_upwards [ht] with w hw
  linarith

end Hindman168
