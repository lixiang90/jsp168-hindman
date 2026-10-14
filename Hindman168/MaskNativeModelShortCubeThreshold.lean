import Hindman168.MaskRenamedShortCubeLaw
import Hindman168.FiniteOrderModelShortCubeThreshold

namespace Hindman168
open Filter FiniteMass MaskOriginalSampling
open scoped Topology Classical
universe u

/-- One quotient scale and positive projection threshold, fixed before N,
control every actual local mask cube. The finite interval inverse inputs
are explicit unproved hypotheses; the sampling transport is exact. -/
theorem mask_native_model_shortCube_threshold (m s : ℕ)
    (hinverse : ∀ d : ℕ, d ≤ maskRowCountBound m →
      HasNativePeriodicIntervalInverse.{u} s (2 ^ d + 2 ^ d - 1))
    (η : ℝ) (hη : 0 < η) :
    ∃ J : ℕ, 0 < J ∧ ∃ κ : ℝ, 0 < κ ∧
      ∀ (N : ℕ) (hN : 0 < N) (l : ℕ) (hl : l < N),
      let gap : ℕ → Fin N := fun _ => ⟨l, hl⟩
      let F := maskGeneratedMaster m gap
      ∀ (t : Fin (Fintype.card (LargeColumnSubset m)))
        (i : ℕ) (_hi : i < N) (_hli : l ≤ i)
        (U : Ultrafilter ℕ) (_hU : (U : Filter ℕ) ≤ atTop)
        (f model : boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)))
        (_hf : ∀ w y, 0 ≤ f.val w y ∧ f.val w y ≤ 1)
        (_hmodel : ∀ w y, 0 ≤ model.val w y ∧ model.val w y ≤ 1),
      ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F i) U
        (masterGapIndex N hN l)).starProjection
          (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U model)‖ < κ →
      ∀ᶠ w in (U : Filter ℕ),
        expectation (conditionMass
          (primeIndependentMass (maskGeneratedRowDataFamily m gap t).arity
            (F.pool w l).lower (F.pool w l).upper)
          (primeSampleGood ((maskGeneratedRowDataFamily m gap t).rows.catalog
            (maskGeneratedRowDataFamily m gap t).target))) (fun x =>
          |integerPredictionShortCubeStatistic w (F.modulus w : ℕ) (F.gap w l) (F.cutoff w i)
            (targetPredictionOrder gap t) J (targetPredictionPolynomial gap t)
            (fun y => f.val w y - model.val w y) x|) < η := by
  obtain ⟨J, hJ, κ, hκ, hthreshold⟩ := finite_order_model_shortCube_threshold
    (Fin (maskRowCountBound m + 1)) s (fun q => q.val)
    (fun q => hinverse q.val (Nat.le_of_lt_succ q.isLt)) η hη
  refine ⟨J, hJ, κ, hκ, ?_⟩
  intro N hN l hl gap F t i hi hli U hU f model hf hmodel hp
  let D := originalRowMasterCatalog (maskGeneratedRowDataFamily m gap)
  let hD := originalRowMasterCatalog_nonzero (maskGeneratedRowDataFamily m gap)
  let pol := MvPolynomial.rename (maskGeneratedRowDataFamily m gap t).slot
    (targetPredictionPolynomial gap t)
  let P := ((maskGeneratedRowDataFamily m gap t).rows.catalog
    (maskGeneratedRowDataFamily m gap t).target).image
      (MvPolynomial.rename (maskGeneratedRowDataFamily m gap t).slot)
  have hden : targetPredictionPolynomial gap t ∈
      (maskGeneratedRowDataFamily m gap t).rows.catalog (maskGeneratedRowDataFamily m gap t).target :=
    (maskGeneratedRowDataFamily m gap t).rows.denominator_mem_catalog _
  have hpol : pol ∈ D := originalRowMasterCatalog_inclusion
    (maskGeneratedRowDataFamily m gap) t _ hden
  have hP : ∀ q ∈ P, q ≠ 0 := maskRenamedLocalCatalog_nonzero m gap t
  have hpolP : pol ∈ P := Finset.mem_image.mpr ⟨_, hden, rfl⟩
  let q : Fin (maskRowCountBound m + 1) :=
    ⟨targetPredictionOrder gap t, Nat.lt_succ_of_le (maskGenerated_additive_dimension_le m gap t)⟩
  have hx := hthreshold q hN D hD pol hpol P hP hpolP l i hl hi hli
    U hU f model hf hmodel hp
  filter_upwards [hx] with w hw
  have he := maskLocal_primeGood_shortCube_eq_renamed m gap t w (F.cutoff w i)
    (targetPredictionOrder gap t) J (fun y => f.val w y - model.val w y)
  rw [he]
  exact hw

end Hindman168
