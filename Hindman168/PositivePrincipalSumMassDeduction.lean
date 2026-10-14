import Hindman168.PositivePrincipalSumMassThresholds

/-! A direct finite-plan / common-Haar / Portmanteau deduction. The source
maps are the actual cumulative jumps. Only their common weak limit is used.
The quantitative loss is exactly 1 / number of fixed plan options. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Topology BigOperators ENNReal NNReal

theorem principal_finite_plan_common_haar_actual_liminf
    {Z X O E K : Type*} [MeasurableSpace Z]
    [MeasurableSpace X] [TopologicalSpace X] [OpensMeasurableSpace X] [HasOuterApproxClosed X]
    [Fintype O] [Nonempty O] {J : O → Type*} [∀ o, Finite (J o)]
    (LE : Filter E) [LE.NeBot] (LK : Filter K)
    (lam : E → ProbabilityMeasure Z) (Y : O → E → Z → X)
    (hY : ∀ o e, Measurable (Y o e)) (μ : ProbabilityMeasure X)
    (hjump : ∀ o, Tendsto (fun e => (lam e).map (hY o e).aemeasurable) LE (𝓝 μ))
    (θ : ℝ) (hθ : 0 < θ) (c t : ∀ o, J o → X → ℝ)
    (hc : ∀ o j, Continuous (c o j)) (ht : ∀ o j, Continuous (t o j))
    (hplan : ∀ᶠ e in LE, ∀ z, ∃ o, ∀ j,
      decide (3*θ/2 < c o j (Y o e z)) = decide (3*θ/2 < t o j (Y o e z)))
    (ν : K → ProbabilityMeasure X) (hactual : Tendsto ν LK (𝓝 μ))
    (c' t' : K → ∀ o, J o → X → ℝ)
    (herr : ∀ᶠ k in LK, (∀ o j x, |c' k o j x - c o j x| < θ/4) ∧
      (∀ o j x, |t' k o j x - t o j x| < θ/4)) :
    ((1 / (Fintype.card O : ℝ≥0) : ℝ≥0) : ℝ≥0∞) ≤
      LK.liminf (fun k => (ν k : Measure X) (principalActualComparisons θ (c' k) (t' k))) := by
  have hclosed := principal_closed_comparisons_isClosed θ c t hc ht
  have hcover : ∀ᶠ e in LE, (1 : ℝ≥0) ≤
      ∑ o, ((lam e).map (hY o e).aemeasurable) (principalClosedComparisons θ c t o) := by
    filter_upwards [hplan] with e he
    apply principal_pointwise_cover_mass (lam e) (fun o => Y o e) (fun o => hY o e)
      (principalClosedComparisons θ c t) (fun o => (hclosed o).measurableSet)
    intro z
    obtain ⟨o, ho⟩ := he z
    exact ⟨o, principal_palette_implies_closed θ c t o (Y o e z) ho⟩
  have hmass := principal_same_limit_closed_union LE
    (fun o e => (lam e).map (hY o e).aemeasurable) μ
    (principalClosedComparisons θ c t) hclosed hjump hcover
  apply principal_closed_mass_yields_actual_liminf LK ν μ hactual θ hθ c t hc ht c' t' herr
  simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using (ENNReal.coe_le_coe.mpr hmass)

/-- A uniform closed-union bound integrates over the original coset mixture.
Only the fixed set is integrated, so no measurable selection of lifts occurs. -/
theorem principal_uniform_closed_mass_mixture {Z X : Type*}
    [MeasurableSpace Z] [MeasurableSpace X]
    (ρ : ProbabilityMeasure Z) (μ : Z → Measure X) (F : Set X) (δ : ℝ≥0∞)
    (h : ∀ᵐ z ∂(ρ : Measure Z), δ ≤ μ z F) :
    δ ≤ ∫⁻ z, μ z F ∂(ρ : Measure Z) := by
  calc
    δ = ∫⁻ _z, δ ∂(ρ : Measure Z) := by simp
    _ ≤ _ := lintegral_mono_ae h

end Hindman168
