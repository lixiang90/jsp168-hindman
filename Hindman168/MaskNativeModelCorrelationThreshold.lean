import Hindman168.MaskNativeModelShortCubeThreshold

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped Topology Classical
universe u

/-- A positive fine-projection threshold fixed before the master count
controls the actual original subset correlation with a tracked F-S target.
Every interval inverse needed by the finite cube-order list remains an
explicit hypothesis. No correlation or target-cube decay is assumed. -/
theorem mask_native_model_original_correlation_threshold (m s : ℕ)
    (hinverse : ∀ d : ℕ, d ≤ maskRowCountBound m →
      HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ (N : ℕ) (hN : 0 < N) (l : ℕ) (hl : l < N),
      let gap : ℕ → Fin N := fun _ => ⟨l, hl⟩
      let F := maskGeneratedMaster m gap
      ∀ (a : Fin (m+1) → ℚ) (_ha : ∀ col, 0 < a col)
        (C : Chain (m+1)) (_hC : ∀ col, C.block col ⊆ Finset.range N)
        (_hgap : ∀ col, l ≤ C.pivot col) (_htail : ∀ col, C.tail col ⊆ Finset.range l)
        (t : Fin (Fintype.card (LargeColumnSubset m))),
      let i := C.pivot (targetRootAnchor gap t)
      ∀ (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (f model : boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)))
        (_hf : ∀ w y, 0 ≤ f.val w y ∧ f.val w y ≤ 1)
        (_hmodel : ∀ w y, 0 ≤ model.val w y ∧ model.val w y ≤ 1)
        (H : ℕ → NonemptyColumnSubset (m+1) → ℤ → ℝ)
        (b : ℕ → Finset (Fin (m+1)) → ℤ → ℝ)
        (_hH : ∀ᶠ w in (U : Filter ℕ), maskOriginalSubsetAdmissible gap (fun _ => C) w (H w) (b w))
        (_htarget : ∀ᶠ w in (U : Filter ℕ),
          H w (maskSourceNonemptySupport m t) = fun y => f.val w y - model.val w y),
      ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F i) U
        (masterGapIndex N hN l)).starProjection
          (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U model)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        |maskOriginalSubsetCorrelation gap a (fun _ => C) w (H w) (b w)| ≤ ε := by
  obtain ⟨δ, hδ, hdetect⟩ := maskOriginalSubset_shortCube_detection_threshold m ε hε
  obtain ⟨J, hJ, κ, hκ, hshort⟩ := mask_native_model_shortCube_threshold m s hinverse δ hδ
  refine ⟨J, hJ, κ, hκ, ?_⟩
  intro N hN l hl gap F a ha C hC hgap htail t i U hU f model hf hmodel H b hH htarget hp
  have hi : i < N := Finset.mem_range.mp (hC (targetRootAnchor gap t)
    (by simp [Chain.block, i]))
  have hli : l ≤ i := hgap (targetRootAnchor gap t)
  have hs := hshort N hN l hl t i hi hli U hU f model hf hmodel hp
  have hd := hdetect gap a ha (fun _ => C) (fun _ => hC) J hJ
    (Eventually.of_forall (fun _ => hgap)) (Eventually.of_forall (fun _ => htail))
  filter_upwards [hU hd, hs, hH, htarget] with w hw hsw hHw htw
  apply hw t (H w) (b w) hHw
  rw [htw]
  exact hsw.le

end Hindman168
