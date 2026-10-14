import Hindman168.FiniteProbabilityMixture
import Hindman168.FiniteComplexSetMean
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-! Genuine empirical probabilities, with an explicit fallback for empty
windows. Their nonempty-window integral uses the actual cardinality. -/
namespace Hindman168
open MeasureTheory
open scoped BigOperators

noncomputable def finiteEmpiricalProbability {Z X : Type*} [MeasurableSpace X]
    (S : Finset Z) (orbit : Z → X) (x₀ : X) : ProbabilityMeasure X := by
  classical
  by_cases hS : S.Nonempty
  · letI : Nonempty S := ⟨⟨hS.choose,hS.choose_spec⟩⟩
    exact ⟨finiteProbabilityMixture (fun z : S => Measure.dirac (orbit z)),
      finite_probability_mixture_isProbability _ (fun _ => inferInstance)⟩
  · exact ⟨Measure.dirac x₀,inferInstance⟩

theorem finite_empirical_probability_integral {Z X : Type*} [MeasurableSpace X]
    [MeasurableSingletonClass X] (S : Finset Z) (hS : S.Nonempty)
    (orbit : Z → X) (x₀ : X) (J : X → ℂ) :
    (∫ x, J x ∂(finiteEmpiricalProbability S orbit x₀)) =
      finiteComplexSetMean S (fun z => J (orbit z)) := by
  classical
  simp only [finiteEmpiricalProbability, dif_pos hS, ProbabilityMeasure.coe_mk]
  rw [finite_probability_mixture_integral _ _ (fun _ => integrable_dirac (by simp))]
  simp only [integral_dirac, finiteComplexMean, finiteComplexSetMean,
    Fintype.card_coe, ← Finset.sum_attach S (fun z => J (orbit z))]
  rfl

end Hindman168
