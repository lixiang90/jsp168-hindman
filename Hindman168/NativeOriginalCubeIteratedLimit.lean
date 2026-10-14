import Hindman168.NativeOriginalCubeBoundedAlpha
import Hindman168.CubeStandardAlphaBox
import Hindman168.IteratedLocalLimsup

/-! The actual paper limit: first length limsup, then alpha down to zero,
for the original source and its actual cube Haar image. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_cube_iterated_limit {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (P : ℕ → ℝ → D.G) (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G)
    (hL : Tendsto L atTop atTop) (hlaw : NativeCubeBoundedAlphaHaarLaw D H L P M hM sigma hRat h)
    (q : Fin (s+2)) (beta : ℝ) (t : ℕ) (ht : 0 < t) (hMt : (M : ℤ) ∣ (t : ℤ)) (b : ℤ) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ f : C((Finset (Fin q.val) → D.G ⧸ D.Γ), ℂ), ∀ T : NNReal, LipschitzWith T f →
      Tendsto (fun α : ℝ => limsup (fun m : ℕ =>
        ‖finiteComplexSetMean (alignmentBoxClass
          (fun j => ⌈cubeAlphaLower q.val beta (L m) j⌉)
          (fun j => ⌈cubeAlphaUpper q.val beta (L m) α j⌉) (cubeAlphaResidue q.val b) t)
          (fun x => f (fun V => (P m ((x 0 + ∑ i ∈ V, x i.succ : ℤ) : ℝ) : D.G ⧸ D.Γ))) -
          ∫ y, f y ∂nativeResidueCubeHaarImage D H (sigma (signedPeriodResidue M hM b)) (hRat _)
            q.val (2^q.val-1) (nativeCubeVertexEnumeration q.val) (h beta)‖) atTop)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : CompactSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_quotient_compact D
  intro f T hf
  apply nonnegative_iterated_local_limsup _ (fun _ _ => norm_nonneg _)
  intro ε hε
  obtain ⟨α0,hα0,ha⟩ := hlaw beta 1 1 zero_lt_one zero_le_one ‖f‖ (norm_nonneg f) T ε hε
  refine ⟨α0,hα0,?_⟩
  intro α hα hα'
  filter_upwards [ha α hα hα' t ht hMt,hL.eventually (eventually_gt_atTop 0)] with m hm hLm
  have hg := cube_standard_alpha_geometry q.val beta (L m) α (mul_nonneg hα.le hLm.le)
  have hv : ∀ i : Fin q.val, (M : ℤ) ∣ cubeAlphaResidue q.val b i.succ := by
    intro i
    simp only [cubeAlphaResidue,Fin.cases_succ,dvd_zero]
  have hlen : ∀ j, 1*α*L m ≤ cubeAlphaUpper q.val beta (L m) α j-cubeAlphaLower q.val beta (L m) j ∧
      cubeAlphaUpper q.val beta (L m) α j-cubeAlphaLower q.val beta (L m) j ≤ 1*α*L m := by
    intro j
    rw [hg.1 j,one_mul]
    exact ⟨le_rfl,le_rfl⟩
  have hh := hm q (cubeAlphaLower q.val beta (L m)) (cubeAlphaUpper q.val beta (L m) α)
    (cubeAlphaResidue q.val b) hv hlen
    (by simpa only [one_mul] using hg.2.1) (by simpa only [one_mul] using hg.2.2)
    f hf f.norm_coe_le_norm
  simpa only [cubeAlphaResidue,Fin.cases_zero] using hh

end Hindman168
