import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic

/-! The finite-option same-Haar argument of (8.23). Every option has its
OWN prelimit law, but all converge to the SAME measure. No invariance of
that prelimit law, nor measurable choice of lifts, is assumed. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

/-- Finite pointwise coverage and common weak limits force one closed option
to have mass at least 1/Q. Q is only the cardinality of the fixed option type. -/
theorem principal_same_limit_closed_cover {X O I : Type*}
    [Fintype O] [Nonempty O] [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (L : Filter I) [L.NeBot] (ν : O → I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (F : O → Set X) (hF : ∀ o, IsClosed (F o))
    (hlim : ∀ o, Tendsto (ν o) L (𝓝 μ))
    (hcover : ∀ᶠ t in L, (1 : ℝ≥0) ≤ ∑ o, ν o t (F o)) :
    ∃ o, (1 / (Fintype.card O : ℝ≥0)) ≤ μ (F o) := by
  classical
  have hcard : (Fintype.card O : ℝ≥0) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : (∑ _o : O, (1 / (Fintype.card O : ℝ≥0))) = 1 := by
    simp [nsmul_eq_mul, hcard]
  have he : ∀ᶠ t in L, ∃ o, (1 / (Fintype.card O : ℝ≥0)) ≤ ν o t (F o) := by
    filter_upwards [hcover] with t ht
    obtain ⟨o, _, ho⟩ := Finset.exists_le_of_sum_le Finset.univ_nonempty (hsum.symm ▸ ht)
    exact ⟨o, ho⟩
  obtain ⟨o, ho⟩ := frequently_exists.mp he.frequently
  refine ⟨o, ?_⟩
  have hf : ∃ᶠ t in L, ((1 / (Fintype.card O : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
      (ν o t : Measure X) (F o) := ho.mono (fun t ht => by
        simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
          (ENNReal.coe_le_coe.mpr ht))
  have h := (le_limsup_of_frequently_le hf).trans
    (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto (hlim o) (hF o))
  apply ENNReal.coe_le_coe.mp
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h

theorem principal_same_limit_closed_union {X O I : Type*}
    [Fintype O] [Nonempty O] [MeasurableSpace X] [TopologicalSpace X]
    [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    (L : Filter I) [L.NeBot] (ν : O → I → ProbabilityMeasure X) (μ : ProbabilityMeasure X)
    (F : O → Set X) (hF : ∀ o, IsClosed (F o))
    (hlim : ∀ o, Tendsto (ν o) L (𝓝 μ))
    (hcover : ∀ᶠ t in L, (1 : ℝ≥0) ≤ ∑ o, ν o t (F o)) :
    (1 / (Fintype.card O : ℝ≥0)) ≤ μ (⋃ o, F o) := by
  obtain ⟨o, ho⟩ := principal_same_limit_closed_cover L ν μ F hF hlim hcover
  apply ho.trans
  apply ENNReal.coe_le_coe.mp
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
    (measure_mono (μ := (μ : Measure X)) (Set.subset_iUnion F o))

/-- The cover inequality is derived from actual maps of one probability law,
exactly as for the original weighted-box shears. -/
theorem principal_pointwise_cover_mass {Z X O : Type*} [Fintype O]
    [MeasurableSpace Z] [MeasurableSpace X]
    (lam : ProbabilityMeasure Z) (Y : O → Z → X) (hY : ∀ o, Measurable (Y o))
    (F : O → Set X) (hF : ∀ o, MeasurableSet (F o))
    (hcover : ∀ z, ∃ o, Y o z ∈ F o) :
    (1 : ℝ≥0) ≤ ∑ o, (lam.map (hY o).aemeasurable) (F o) := by
  have hunion : (⋃ o, Y o ⁻¹' F o) = Set.univ := by
    ext z
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_univ, iff_true]
    exact hcover z
  have h := measure_iUnion_fintype_le (lam : Measure Z) (fun o => Y o ⁻¹' F o)
  rw [hunion, measure_univ] at h
  have he (o) : (lam : Measure Z) (Y o ⁻¹' F o) =
      ((lam.map (hY o).aemeasurable : ProbabilityMeasure X) : Measure X) (F o) :=
    (ProbabilityMeasure.map_apply' lam (hY o).aemeasurable (hF o)).symm
  simp_rw [he] at h
  apply ENNReal.coe_le_coe.mp
  simpa only [ENNReal.ofNNReal_finsetSum, ENNReal.coe_one, ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using h

end Hindman168
