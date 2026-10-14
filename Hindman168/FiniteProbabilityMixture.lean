import Hindman168.FiniteComplexMean
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-! The actual uniform finite mixture of measures and its complex integral. -/
namespace Hindman168
open MeasureTheory
open scoped BigOperators ENNReal

noncomputable def finiteProbabilityMixture {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : I → Measure X) : Measure X := (Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, μ i

theorem finite_probability_mixture_isProbability {I X : Type*} [Fintype I] [Nonempty I]
    [MeasurableSpace X] (μ : I → Measure X) (hμ : ∀ i, IsProbabilityMeasure (μ i)) :
    IsProbabilityMeasure (finiteProbabilityMixture μ) := by
  letI := hμ
  constructor
  simp only [finiteProbabilityMixture, Measure.smul_apply, Measure.finsetSum_apply,
    measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero (α := I)) (by simp)

theorem finite_probability_mixture_integral {I X : Type*} [Fintype I] [MeasurableSpace X]
    (μ : I → Measure X) (f : X → ℂ) (hf : ∀ i, Integrable f (μ i)) :
    (∫ x, f x ∂finiteProbabilityMixture μ) = finiteComplexMean (fun i => ∫ x, f x ∂μ i) := by
  rw [finiteProbabilityMixture, integral_smul_measure, integral_finsetSum_measure (fun i _ => hf i)]
  simp only [finiteComplexMean, ENNReal.toReal_inv, ENNReal.toReal_natCast, Complex.real_smul,
    Complex.ofReal_inv, Complex.ofReal_natCast]
  ring

end Hindman168
