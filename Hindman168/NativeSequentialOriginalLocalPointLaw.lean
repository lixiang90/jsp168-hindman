import Hindman168.NativeOriginalRealLocalHaar
import Hindman168.NativeRationalLayerHaarContinuity

/-! The original adapted polynomial sequence has a genuine local point law
on ONE selected subsequence. All residues share its filtration, period and
smooth curve; expectations of the actual Haar images vary continuously. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_original_local_point_law {s ℓ : ℕ}
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
        NativeResidueLocalHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h ∧
        NativeRealLocalHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M sigma hRat h ∧
        ∀ r : Fin M, ∀ J : C(D.G ⧸ D.Γ,ℂ),
          Continuous (fun beta => ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨f,hf,hLf,H,q,as,c,gamma,cLimit,K,hle,_,hsource,hirr,hcoeff,_,hc,_,hgamma,hidentity,
      M,hM,sigma,hRat,hPattern⟩ := native_sequential_adapted_periodic_factorization D F L hL p hp
  obtain ⟨h,hh,hlaw⟩ := native_original_residue_local_haar D H (L ∘ f) hLf q
    (fun n => (hsource n).1) hirr c cLimit hc as (fun a ha => (hcoeff a ha).2)
    (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) gamma hgamma hidentity M hM sigma hRat hPattern
  refine ⟨f,hf,hLf,H,hle,M,hM,sigma,hRat,h,hh,hlaw,
    native_original_real_local_haar D H (L ∘ f) hLf _ M hM sigma hRat h hlaw,?_⟩
  intro r J
  exact native_rational_layer_haar_integral_continuous D H 0 (sigma r) (hRat r) h hh.continuous J

end Hindman168
