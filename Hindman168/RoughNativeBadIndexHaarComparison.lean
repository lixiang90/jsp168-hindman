import Hindman168.NativeNilmanifoldProbabilityTesting
import Hindman168.RoughNativeComplexBadIndex
import Hindman168.FiniteComplexMassMean

namespace Hindman168
open MeasureTheory
open scoped Classical
universe u

/-- The ACTUAL original bad pair produces Haar discrepancy on at least
one ORIGINAL sample, retaining its original observable and box geometry. -/
theorem rough_native_complex_bad_index_haar_comparison {κ : Type*} [Fintype κ] {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (Q : (Option κ → ℝ) → D.G)
    (z t : ℕ) (Z c C : ℝ) (L : NNReal) (B η : ℝ)
    (hbad : RoughNativeComplexBadIndex D Q z t Z c C L B η) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ (lo hi v : κ → ℤ) (F : C(D.G ⧸ D.Γ, ℂ)),
      LipschitzWith L F ∧ (∀ x, ‖F x‖ ≤ B) ∧
      (∀ j, c*Z ≤ (hi j : ℝ)-lo j ∧ (hi j : ℝ)-lo j ≤ C*Z ∧
        |(lo j : ℝ)| ≤ C*Z ∧ |(hi j : ℝ)| ≤ C*Z) ∧
      0 < (alignmentBoxClass lo hi v t).card ∧
      0 < (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j))).card ∧
      (η/2 < ‖finiteComplexSetMean (alignmentBoxClass lo hi v t)
        (fun y => F (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))) : D.G ⧸ D.Γ)) -
          ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ ∨
       η/2 < ‖finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j)))
        (fun y => F (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))) : D.G ⧸ D.Γ)) -
          ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨lo, hi, v, f, hL, hB, hbox, hstep, hfull, hpair⟩ := hbad
  let F : C(D.G ⧸ D.Γ, ℂ) := ⟨f, hL.continuous⟩
  refine ⟨lo, hi, v, F, hL, hB, hbox, hstep, hfull, ?_⟩
  rw [FiniteMass.complexExpectation_uniformFinset, FiniteMass.complexExpectation_uniformFinset] at hpair
  exact native_probability_pair_discrepancy_split D (alignmentBoxClass lo hi v t)
    (Fintype.piFinset (fun j => Finset.Ico (lo j) (hi j)))
    (fun y => (Q (Option.elim · (z : ℝ) (fun j => (y j : ℝ))) : D.G ⧸ D.Γ)) F η hpair

end Hindman168
