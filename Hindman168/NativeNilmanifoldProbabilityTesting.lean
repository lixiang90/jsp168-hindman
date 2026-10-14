import Hindman168.NativeNilmanifoldQuotientProbability
import Hindman168.FiniteComplexSetMean
import Mathlib.MeasureTheory.Group.Integral

namespace Hindman168
open MeasureTheory Measure
open scoped Manifold ContDiff
universe u

theorem native_nilmanifold_probability_integrable {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ F : C(D.G ⧸ D.Γ, ℂ), Integrable F (nativeNilmanifoldQuotientProbability D) := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI := native_nilmanifold_quotient_probability_isProbability D
  intro F
  exact F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)

theorem native_nilmanifold_probability_integral_bound {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ (F : (D.G ⧸ D.Γ) → ℂ) (B : ℝ), (∀ x, ‖F x‖ ≤ B) →
      ‖∫ x, F x ∂nativeNilmanifoldQuotientProbability D‖ ≤ B := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI := native_nilmanifold_quotient_probability_isProbability D
  intro F B hB
  have h := norm_integral_le_of_norm_le_const (μ := nativeNilmanifoldQuotientProbability D)
    (Filter.Eventually.of_forall hB)
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using h

theorem native_nilmanifold_probability_integral_translation {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (g : D.G) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ F : (D.G ⧸ D.Γ) → ℂ,
      (∫ x, F (g • x) ∂nativeNilmanifoldQuotientProbability D) =
        ∫ x, F x ∂nativeNilmanifoldQuotientProbability D := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  letI : BorelSpace D.G := ⟨rfl⟩
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_coset_borel D
  letI := native_nilmanifold_quotient_probability_invariant D
  exact fun F => integral_smul_eq_self F

theorem native_probability_pair_discrepancy_split {α : Type*} {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (a b : Finset α) (f : α → D.G ⧸ D.Γ) :
    letI : MeasurableSpace D.E := borel D.E
    letI : MeasurableSpace D.G := borel D.G
    ∀ (F : (D.G ⧸ D.Γ) → ℂ) (η : ℝ),
      η < ‖finiteComplexSetMean a (fun x => F (f x)) - finiteComplexSetMean b (fun x => F (f x))‖ →
      η/2 < ‖finiteComplexSetMean a (fun x => F (f x)) - ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ ∨
      η/2 < ‖finiteComplexSetMean b (fun x => F (f x)) - ∫ q, F q ∂nativeNilmanifoldQuotientProbability D‖ := by
  letI : MeasurableSpace D.E := borel D.E
  letI : MeasurableSpace D.G := borel D.G
  intro F η hbad
  let A := finiteComplexSetMean a (fun x => F (f x))
  let B := finiteComplexSetMean b (fun x => F (f x))
  let C := ∫ q, F q ∂nativeNilmanifoldQuotientProbability D
  have htriangle : ‖A-B‖ ≤ ‖A-C‖+‖B-C‖ := by
    calc
      _ = ‖(A-C)-(B-C)‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  by_contra h
  push Not at h
  linarith only [hbad, htriangle, h.1, h.2]

end Hindman168
