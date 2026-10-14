import Hindman168.NativeOriginalCubeLocalHaar

/-! One descent and one subsequence produce local ORIGINAL-source cube laws
simultaneously through the ORIGINAL nilpotency bound, with one common period,
filtration and smooth curve. No cube-dependent refactorization is performed. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_original_local_cube_law {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (p : ℕ → RoughVectorMvPolynomial Unit D.E)
    (hp : ∀ n, RoughVectorMvWeightedDegree F.layer (p n) 0) :
    letI : MeasurableSpace D.G := borel D.G
    letI := D.metric
    letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
    ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (L ∘ f) atTop atTop ∧
      ∃ H : NativeRationalSubgroupFiltration D ℓ, (∀ k, H.layer k ≤ F.layer k) ∧
      ∃ M : ℕ, ∃ hM : 0 < M, ∃ sigma : Fin M → D.G,
      ∃ hRat : ∀ r, sigma r ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ,
      ∃ h : ℝ → D.G, ContMDiff 𝓘(ℝ) D.I ∞ h ∧
        NativeCubeLocalHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,_,hsource,hirr,hcoeff,_,hc,_,hgamma,hidentity,
      M,hM,sigma,hRat,hPattern⟩ := native_sequential_adapted_periodic_factorization D F L hL p hp
  obtain ⟨h,hh,hlaw⟩ := native_original_cube_local_haar D H (L ∘ f) hLf q
    (fun n => (hsource n).1) hirr c cLimit hc as (fun a ha => (hcoeff a ha).2)
    (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) gamma hgamma hidentity M hM sigma hRat hPattern
  exact ⟨f,hf,hLf,H,hle,M,hM,sigma,hRat,h,hh,hlaw⟩

end Hindman168
