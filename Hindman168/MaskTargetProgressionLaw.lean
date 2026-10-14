import Hindman168.MaskTargetUniformAnchorError

/-! The actual prime, direction-pair and remaining harmonic laws used in the
anchor comparison. Every probability normalization is derived from source
sampling, and the original cube average is reindexed exactly. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def rootPrimeMass (w : ℕ) : Mass (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) :=
  conditionMass (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
    (maskGeneratedCopiedPrimeGood m gap t w)

theorem rootPrimeMass_probability_eventually :
    ∀ᶠ w in atTop, (∀ x, 0 ≤ rootPrimeMass gap t w x) ∧ total (rootPrimeMass gap t w) = 1 := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [(maskGeneratedCopiedGood_event_tendsto_one m gap t).eventually
    (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1))] with w hw
  exact ⟨conditionMass_nonneg _ _ (hF.prime_slots_nonneg w (fun _ => (gap w).val)),
    conditionMass_total _ _ hw⟩

include hC in
theorem rootRestMass_probability_eventually :
    ∀ᶠ w in atTop, (∀ rest, 0 ≤ rootRestMass gap C t w rest) ∧ total (rootRestMass gap C t w) = 1 := by
  filter_upwards [base_coordinates_probability_eventually gap C hC] with w hw
  unfold rootRestMass
  exact ⟨piMass_nonneg _ (fun col => (hw col.val).1), piMass_total_one _ (fun col => (hw col.val).2)⟩

theorem directionPairMass_probability_eventually (J : ℕ) (hJ : 0 < J) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      (∀ v, 0 ≤ MaskRootOriginalSampling.directionPairMass gap t J w x v) ∧
        total (MaskRootOriginalSampling.directionPairMass gap t J w x) = 1 := by
  filter_upwards [maskGeneratedShiftLength_eventually_pos m gap t J hJ] with w hw
  intro x hx
  unfold MaskRootOriginalSampling.directionPairMass
  refine ⟨piMass_nonneg _ (fun _ => tensor_nonneg _ _
    (uniformIntervalMass_nonneg _ _) (uniformIntervalMass_nonneg _ _)), piMass_total_one _ ?_⟩
  intro _
  rw [tensor_total, uniformIntervalMass_total 0 (hw x hx), one_mul]

noncomputable def targetAnchorAverage
    (J : ℕ)
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (rootPrimeMass gap t w) (fun x =>
    expectation (MaskRootOriginalSampling.directionPairMass gap t J w x) (fun v =>
      expectation (rootRestMass gap C t w) (fun rest =>
        expectation (integerMass ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w))
          (fun y => targetCube gap a C t F w (x, insertPivotCoordinate (targetRootAnchor gap t) rest y) v))))

noncomputable def targetProgressionAverage
    (J : ℕ)
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) : ℝ :=
  expectation (rootPrimeMass gap t w) (fun x =>
    expectation (MaskRootOriginalSampling.directionPairMass gap t J w x) (fun v =>
      expectation (rootRestMass gap C t w) (fun rest =>
        expectation (integerProgressionMass
          ((maskGeneratedMaster m gap).cutoff w ((C w).pivot (targetRootAnchor gap t))) (primorial w)
          (targetRootMultiplier gap t x) (targetRootOffset gap a C t w x rest v))
          (rootCubeTest gap t F w x v))))

theorem targetCubeAverage_eq_targetAnchorAverage (J : ℕ) (hJ : 0 < J)
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col)
    (F : ℕ → (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) → MaskOriginalBaseRow m gap t → ℤ → ℝ)
    (w : ℕ) :
    targetCubeAverage gap a ha C hC t J hJ hgap F w = targetAnchorAverage gap a C t J F w := by
  rw [targetCubeAverage_eq_native, MaskRootOriginalSampling.expectation_nativeJointMass]
  change expectation (rootPrimeMass gap t w) (fun x =>
    expectation (maskOriginalBaseMass m gap C w) (fun z =>
      expectation (MaskRootOriginalSampling.directionPairMass gap t J w x) (fun v => targetCube gap a C t F w (x, z) v))) = _
  unfold targetAnchorAverage
  apply congrArg (expectation (rootPrimeMass gap t w))
  funext x
  rw [expectation_comm]
  apply congrArg (expectation (MaskRootOriginalSampling.directionPairMass gap t J w x))
  funext v
  exact targetCube_base_average_eq_pivot gap a C t F w x v

end Hindman168.MaskOriginalSampling
