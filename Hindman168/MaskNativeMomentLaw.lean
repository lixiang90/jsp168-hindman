import Hindman168.MaskRootMixedProfileProducts

/-! Native original joint mass for the three paper moments. Its prime,
harmonic and conditional quotient coefficients are the original ones. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskRootOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (t : Fin (Fintype.card (LargeColumnSubset m))) (J : ℕ)

abbrev NativeMomentPoint (m : ℕ) {N : ℕ} (gap : ℕ → Fin N)
    (t : Fin (Fintype.card (LargeColumnSubset m))) :=
  (Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) ×
    ((Fin (m + 1) → ℤ) × (MaskOriginalDirection m gap t → ℤ × ℤ))

noncomputable def nativeJointMass (w : ℕ) : Mass (NativeMomentPoint m gap t) :=
  conditionalJoint
    (conditionMass (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
      (maskGeneratedCopiedPrimeGood m gap t w))
    (fun x => tensor (maskOriginalBaseMass m gap C w) (directionPairMass gap t J w x))

theorem expectation_nativeJointMass (w : ℕ) (f : NativeMomentPoint m gap t → ℝ) :
    expectation (nativeJointMass gap C t J w) f =
      expectation (conditionMass (masterPrimeSlotsMass (maskGeneratedMaster m gap) w (fun _ => (gap w).val))
        (maskGeneratedCopiedPrimeGood m gap t w)) (fun x =>
          expectation (maskOriginalBaseMass m gap C w) (fun z =>
            expectation (directionPairMass gap t J w x) (fun v => f (x, z, v)))) := by
  unfold nativeJointMass
  rw [expectation_conditionalJoint]
  simp_rw [expectation_tensor]

theorem nativeJointMass_eventually_nonneg
    (hC : ∀ w col, (C w).block col ⊆ Finset.range N) :
    ∀ᶠ w in atTop, ∀ p, 0 ≤ nativeJointMass gap C t J w p := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [MaskOriginalSampling.base_probability_eventually gap C hC] with w hb
  unfold nativeJointMass
  apply conditionalJoint_nonneg _ _
    (conditionMass_nonneg _ _ (hF.prime_slots_nonneg w (fun _ => (gap w).val)))
  intro x _
  apply tensor_nonneg _ _ hb.1
  exact piMass_nonneg _ (fun _ => tensor_nonneg _ _
    (uniformIntervalMass_nonneg _ _) (uniformIntervalMass_nonneg _ _))

variable (a : Fin (m + 1) → ℚ)

noncomputable def nativeB (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (p : NativeMomentPoint m gap t) : ℝ :=
  targetMajorantCube gap a C t label w p.1 p.2.1 p.2.2

noncomputable def nativeH (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (p : NativeMomentPoint m gap t) : ℝ :=
  MaskOriginalSampling.smoothedRetainedMajorant gap a C t label w (p.1, p.2.1) p.2.2

noncomputable def nativeFirstMoment (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) : ℝ :=
  expectation (nativeJointMass gap C t J w) (fun p => nativeB gap C t a label w p * nativeH gap C t a label w p)

noncomputable def nativeSecondMoment (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) : ℝ :=
  expectation (nativeJointMass gap C t J w) (fun p => nativeB gap C t a label w p * nativeH gap C t a label w p ^ 2)

theorem nativeB_average_eq (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1)) (w : ℕ) :
    expectation (nativeJointMass gap C t J w) (nativeB gap C t a label w) =
      targetMajorantAverage gap a C t J label w := by
  rw [expectation_nativeJointMass]
  rfl

theorem nativeH_root_expectation_eq
    (label : ℕ → MaskOriginalBaseRow m gap t → Fin (m + 1))
    (w : ℕ) (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (z : Fin (m + 1) → ℤ) (v : MaskOriginalDirection m gap t → ℤ × ℤ) :
    expectation (MaskOriginalSampling.rootMass (m := m) gap w)
      (shiftedRetainedProfile gap a C t label w x z v) = nativeH gap C t a label w (x, z, v) := rfl

end Hindman168.MaskRootOriginalSampling
