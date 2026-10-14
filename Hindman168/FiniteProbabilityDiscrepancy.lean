import Hindman168.FiniteComplexSetMean
import Hindman168.LinearDiscrepancyStability
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! A finite empirical mean minus an ACTUAL probability integral, uniformly
bounded in the continuous-test norm, even for an algebraically empty sample. -/
namespace Hindman168
open MeasureTheory
open scoped Classical

noncomputable def finiteProbabilityDiscrepancy {X α : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (S : Finset α) (x : α → X) : C(X,ℂ) →ₗ[ℂ] ℂ where
  toFun F := finiteComplexSetMean S (fun a => F (x a)) - ∫ y, F y ∂μ
  map_add' F G := by
    have hi (f : C(X,ℂ)) : Integrable f μ :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
    simp only [ContinuousMap.add_apply,finiteComplexSetMean,Finset.sum_add_distrib,add_div,integral_add (hi F) (hi G)]
    ring
  map_smul' c F := by
    simp only [ContinuousMap.smul_apply,finiteComplexSetMean,← Finset.smul_sum,smul_div_assoc,
      integral_smul,smul_sub,RingHom.id_apply]

theorem finite_probability_discrepancy_norm {X α : Type*} [MetricSpace X] [CompactSpace X]
    [MeasurableSpace X] [BorelSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (S : Finset α) (x : α → X) (F : C(X,ℂ)) :
    ‖finiteProbabilityDiscrepancy μ S x F‖ ≤ 2*‖F‖ := by
  have hm := finiteComplexSetMean_norm_bound S (fun a => F (x a)) ‖F‖ (norm_nonneg F)
    (fun a _ => F.norm_coe_le_norm (x a))
  have hi : ‖∫ y, F y ∂μ‖ ≤ ‖F‖ := by
    have h := norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall F.norm_coe_le_norm)
    simpa only [Measure.real,measure_univ,ENNReal.toReal_one,mul_one] using h
  change ‖finiteComplexSetMean S (fun a => F (x a)) - ∫ y, F y ∂μ‖ ≤ _
  exact (norm_sub_le _ _).trans (by linarith only [hm,hi])

end Hindman168
