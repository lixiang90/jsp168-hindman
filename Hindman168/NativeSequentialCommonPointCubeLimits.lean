import Hindman168.NativeOriginalGivenPointHaar
import Hindman168.NativeOriginalGivenCubeHaar
import Hindman168.NativeOriginalCubeIteratedLimit
import Hindman168.NativeOriginalContinuousPointMixture

/-! ONE original factorization and ONE chosen smooth curve simultaneously give
point local laws, original cube laws, their alpha limits, and the actual global
point-mixture weak limit. No independent existential witnesses are identified. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_common_point_cube_limits {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    letI : BorelSpace (D.G ⧸ D.Γ) := native_nilmanifold_metric_coset_borel D
    ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (L ∘ f) atTop atTop ∧
      ∃ H : NativeRationalSubgroupFiltration D ℓ, (∀ k, H.layer k ≤ F.layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → D.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ,
      ∃ h : ℝ → D.G, ∃ hh : ContMDiff 𝓘(ℝ) D.I ∞ h,
        NativeResidueLocalHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h ∧
        NativeRealLocalHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M sigma hRat h ∧
        NativeCubeLocalHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h ∧
        NativeCubeBoundedAlphaHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h ∧
        (∀ r : Fin M, ∀ J : C(D.G ⧸ D.Γ,ℂ),
          Continuous (fun beta => ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta))) ∧
        Tendsto (fun n => finiteEmpiricalProbability (Finset.Ico 0 ⌊L (f n)⌋)
          (fun z => (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => (z : ℝ))) : D.G ⧸ D.Γ))
          (1 : D.G)) atTop
          (𝓝 (nativePointMixtureProbability D H M hM sigma hRat h hh.continuous)) ∧
        ∀ J : C(D.G ⧸ D.Γ,ℂ),
          Tendsto (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L (f n)⌋)
            (fun z => J (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => (z : ℝ))) : D.G ⧸ D.Γ))) atTop
            (𝓝 (finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1,
              ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)))) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,_,hsource,hirr,hcoeff,_,hc,_,hgamma,hidentity,
      M,hM,sigma,hRat,hPattern⟩ := native_sequential_adapted_periodic_factorization D F L hL p hp
  obtain ⟨h,hh,hfreeze⟩ := native_common_smooth_curve D (L ∘ f) hLf c cLimit hc as
    (fun a ha => (hcoeff a ha).2)
  let P : ℕ → ℝ → D.G := fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
    (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))
  have hpoint := native_original_given_point_haar D H (L ∘ f) hLf q
    (fun n => (hsource n).1) hirr c as h hfreeze P gamma hgamma hidentity M hM sigma hRat hPattern
  have hcube := native_original_given_cube_haar D H (L ∘ f) hLf q
    (fun n => (hsource n).1) hirr c as h hfreeze P gamma hgamma hidentity M hM sigma hRat hPattern
  have halpha := native_cube_alpha_bounded_tests D H (L ∘ f) P M hM sigma hRat h
    (native_cube_local_to_alpha_haar D H (L ∘ f) P M hM sigma hRat h hLf hcube)
  refine ⟨f,hf,hLf,H,hle,M,hM,sigma,hRat,h,hh,hpoint,
    native_original_real_local_haar D H (L ∘ f) hLf P M hM sigma hRat h hpoint,
    hcube,halpha,?_,?_,?_⟩
  · intro r J
    exact native_rational_layer_haar_integral_continuous D H 0 (sigma r) (hRat r) h hh.continuous J
  · exact native_original_point_weak_limit D H (L ∘ f) hLf P M hM sigma hRat h hh.continuous hpoint
  · exact native_original_continuous_point_mixture D H (L ∘ f) hLf P M hM sigma hRat h hh.continuous hpoint

end Hindman168
