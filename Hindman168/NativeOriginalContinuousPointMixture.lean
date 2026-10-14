import Hindman168.NativeOriginalPointWeakLimit

/-! The original global point-mixture formula for EVERY continuous complex
observable, without a Lipschitz assumption or a new subsequence. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_continuous_point_mixture {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → D.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h)
    (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ J : C(D.G ⧸ D.Γ,ℂ),
      Tendsto (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L n⌋)
        (fun z => J (P n (z : ℝ) : D.G ⧸ D.Γ))) atTop
        (𝓝 (finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1,
          ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)))) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro J
  have hw := native_original_point_weak_limit D H L hL P M hM sigma hRat h hh hlaw
  have ht := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hw
    (BoundedContinuousFunction.mkOfCompact J)
  have heq : (fun n => ∫ x, J x ∂(finiteEmpiricalProbability (Finset.Ico 0 ⌊L n⌋)
      (fun z => (P n (z : ℝ) : D.G ⧸ D.Γ)) (1 : D.G))) =ᶠ[atTop]
      (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L n⌋)
        (fun z => J (P n (z : ℝ) : D.G ⧸ D.Γ))) := by
    filter_upwards [hL.eventually_ge_atTop 1] with n hn
    apply finite_empirical_probability_integral
    exact Finset.nonempty_Ico.mpr
      (lt_of_lt_of_le Int.zero_lt_one (Int.le_floor.mpr (by simpa using hn)))
  change Tendsto (fun n => ∫ x, J x ∂(finiteEmpiricalProbability (Finset.Ico 0 ⌊L n⌋)
      (fun z => (P n (z : ℝ) : D.G ⧸ D.Γ)) (1 : D.G))) atTop
      (𝓝 (∫ x, J x ∂nativePointMixtureMeasure D H M sigma hRat h)) at ht
  rw [native_point_mixture_integral D H M sigma hRat h hh J] at ht
  exact ht.congr' heq

end Hindman168
