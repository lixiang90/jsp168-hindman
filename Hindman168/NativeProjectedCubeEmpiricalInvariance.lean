import Hindman168.NativeOriginalContinuousCubeWindows
import Hindman168.LocalEmpiricalMeasureInvariance

/-! Genuine original cube local limits transfer actual projected empirical
comparisons to Haar invariance. The comparison premise remains to be discharged
from the selected alignment arrays; this alone is not face invariance. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_projected_cube_empirical_invariance {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G)
    (hL : Tendsto L atTop atTop) (hlaw : NativeCubeBoundedAlphaHaarLaw D H L P M hM sigma hRat h)
    {Y : Type*} [MetricSpace Y] [CompactSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (q : Fin (s+2)) (beta : ℝ) (t : ℕ) (ht : 0 < t) (hMt : (M : ℤ) ∣ (t : ℤ)) (b : ℤ) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ π : C((Finset (Fin q.val) → D.G ⧸ D.Γ), Y),
    ∀ T : Y → Y, Continuous T →
    (∀ α : ℝ, 0 < α → ∀ F : C(Y,ℂ), ∀ K : NNReal, LipschitzWith K F →
      Tendsto (fun m =>
        finiteComplexSetMean (alignmentBoxClass (fun j => ⌈cubeAlphaLower q.val beta (L m) j⌉) (fun j => ⌈cubeAlphaUpper q.val beta (L m) α j⌉) (cubeAlphaResidue q.val b) t) (fun x => F (T (π (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))))) -
        finiteComplexSetMean (alignmentBoxClass (fun j => ⌈cubeAlphaLower q.val beta (L m) j⌉) (fun j => ⌈cubeAlphaUpper q.val beta (L m) α j⌉) (cubeAlphaResidue q.val b) t) (fun x => F (π (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))))) atTop (𝓝 0)) →
    Measure.map T (Measure.map π (nativeResidueCubeHaarImage D H (sigma (signedPeriodResidue M hM b)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta))) = Measure.map π (nativeResidueCubeHaarImage D H (sigma (signedPeriodResidue M hM b)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
  intro π T hT hcompare
  let μ := nativeResidueCubeHaarImage D H (sigma (signedPeriodResidue M hM b)) (hRat _) q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)
  letI : IsProbabilityMeasure μ := native_residue_cube_haar_isProbability D H _ _ _ _ _ _
  exact local_empirical_projected_measure_invariant μ
    (fun α m => alignmentBoxClass (fun j => ⌈cubeAlphaLower q.val beta (L m) j⌉) (fun j => ⌈cubeAlphaUpper q.val beta (L m) α j⌉) (cubeAlphaResidue q.val b) t)
    (fun m x => (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ)))
    (native_original_continuous_cube_window D H L P M hM sigma hRat h hL hlaw q beta t ht hMt b)
    π T hT hcompare

end Hindman168
