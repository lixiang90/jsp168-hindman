import Hindman168.NativeOriginalPointMixture
import Hindman168.NativePointMixtureMeasure
import Hindman168.UnitLipschitzProbabilityConvergence
import Hindman168.FiniteEmpiricalProbability

/-! Weak probability convergence of the actual original floor-window orbit. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativePointMixtureProbability {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h) :
    letI : MeasurableSpace D.G := borel D.G
    ProbabilityMeasure (D.G ⧸ D.Γ) := by
  letI : MeasurableSpace D.G := borel D.G
  exact ⟨nativePointMixtureMeasure D H M sigma hRat h,
    native_point_mixture_isProbability D H M hM sigma hRat h hh⟩

theorem native_original_point_weak_limit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → D.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h)
    (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
    Tendsto (fun n => finiteEmpiricalProbability (Finset.Ico 0 ⌊L n⌋)
      (fun z => (P n (z : ℝ) : D.G ⧸ D.Γ)) (1 : D.G)) atTop
      (𝓝 (nativePointMixtureProbability D H M hM sigma hRat h hh)) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  apply unit_lipschitz_probability_tendsto
  intro J hJ
  have ht := native_original_point_mixture D H L hL P M hM sigma hRat h hh hlaw J hJ
  have he : ∀ᶠ n in atTop, (Finset.Ico 0 ⌊L n⌋).Nonempty := by
    filter_upwards [hL.eventually_ge_atTop 1] with n hn
    exact Finset.nonempty_Ico.mpr (lt_of_lt_of_le Int.zero_lt_one (Int.le_floor.mpr (by simpa using hn)))
  have heq : (fun n => ∫ x, J x ∂(finiteEmpiricalProbability (Finset.Ico 0 ⌊L n⌋)
      (fun z => (P n (z : ℝ) : D.G ⧸ D.Γ)) (1 : D.G))) =ᶠ[atTop]
      (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L n⌋)
        (fun z => J (P n (z : ℝ) : D.G ⧸ D.Γ))) := by
    filter_upwards [he] with n hn
    exact finite_empirical_probability_integral _ hn _ _ J
  change Tendsto _ atTop (𝓝 (∫ x, J x ∂nativePointMixtureMeasure D H M sigma hRat h))
  rw [native_point_mixture_integral D H M sigma hRat h hh J]
  exact ht.congr' heq.symm

end Hindman168
