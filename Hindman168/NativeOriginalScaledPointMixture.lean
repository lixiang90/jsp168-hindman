import Hindman168.NativeOriginalTaggedPointMesh
import Hindman168.RealMeshComplexAverage

/-! The original point-mixture formula at real normalization L and the
exact integer window 0<=z<L. All meshes and tags precede the length limit. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_scaled_point_mixture {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (H : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop) (P : ℕ → ℝ → D.G)
    (M : ℕ) (hM : 0 < M) (sigma : Fin M → D.G)
    (hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (h : ℝ → D.G) (hh : Continuous h)
    (hlaw : NativeResidueLocalHaarLaw D H L P M hM sigma hRat h) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∀ J ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
      Tendsto (fun n => (∑ z ∈ Finset.Ico 0 ⌈L n⌉, J (P n (z : ℝ) : D.G ⧸ D.Γ))/(L n : ℂ)) atTop
        (𝓝 (finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1,
          ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)))) := by
  classical
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  letI : Nonempty (Fin M) := ⟨⟨0,hM⟩⟩
  intro J hJ
  let g : Fin M → ℝ → ℂ := fun r beta =>
    ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)
  have hgb (r : Fin M) (beta : ℝ) : ‖g r beta‖ ≤ 1 := by
    letI := native_rational_layer_haar_image_isProbability D H 0 (sigma r) (hRat r) (h beta)
    have hb := norm_integral_le_of_norm_le_const
      (μ := nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta))
      (Filter.Eventually.of_forall hJ.2)
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using hb
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N,hN,tag,hint,hmean⟩ := native_original_tagged_point_mesh D H L hL P M hM sigma hRat h hh hlaw J hJ δ hδ
  let v : Fin N × Fin M → ℂ := fun z => g z.2 (tag z.1)
  have hav : ‖finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1, g r beta) -
      finiteComplexMean v‖ ≤ δ := by
    have hb := finiteComplexMean_norm_le_of_bound
      (fun r : Fin M => (∫ beta in (0 : ℝ)..1, g r beta) - (∑ i : Fin N, g r (tag i))/(N : ℂ)) δ hint
    have he : finiteComplexMean (fun r : Fin M => (∫ beta in (0 : ℝ)..1, g r beta) -
        (∑ i : Fin N, g r (tag i))/(N : ℂ)) =
        finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1, g r beta)-finiteComplexMean v := by
      simp only [finiteComplexMean, Finset.sum_sub_distrib, sub_div, v,
        Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Fintype.sum_prod_type]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_div]
      ring
    rwa [he] at hb
  filter_upwards [hmean,hL.eventually (eventually_gt_atTop (4*(N : ℝ)*M*(δ+1)/ε)),
    hL.eventually (eventually_gt_atTop 0)] with n hn hLarge hLn
  have hb := real_mesh_complex_average_error (L n) hLn N M hN hM
    (fun z => J (P n (z : ℝ) : D.G ⧸ D.Γ)) v δ hδ.le
    (fun z => (hn z.1 z.2).le) (fun z => hgb z.2 (tag z.1))
  have hsmall : 2*(N : ℝ)*M*(δ+1)/L n < ε/2 := by
    apply (div_lt_iff₀ hLn).mpr
    have he := (div_lt_iff₀ hε).mp hLarge
    nlinarith
  have ht := dist_triangle
    ((∑ z ∈ Finset.Ico 0 ⌈L n⌉, J (P n (z : ℝ) : D.G ⧸ D.Γ))/(L n : ℂ))
    (finiteComplexMean v) (finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1, g r beta))
  rw [norm_sub_rev] at hav
  simp only [dist_eq_norm] at ht ⊢
  change ‖_ - finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1, g r beta)‖ < ε
  dsimp [δ] at hb hav hsmall
  linarith

end Hindman168
