import Hindman168.NativeSequentialOriginalLocalCubeLaw
import Hindman168.NativeOriginalCubeIteratedLimit

/-! The original sequence supplies both radius and explicit bounded-test alpha
cube laws on the SAME subsequence, filtration, period, residues and smooth curve. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_original_alpha_cube_law {s ℓ : ℕ}
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
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h ∧
        NativeCubeBoundedAlphaHaarLaw D H (L ∘ f)
          (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b))) M hM sigma hRat h := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨f,hf,hLf,H,hle,M,hM,sigma,hRat,h,hh,hlaw⟩ :=
    native_sequential_original_local_cube_law D F L hL p hp
  refine ⟨f,hf,hLf,H,hle,M,hM,sigma,hRat,h,hh,hlaw,?_⟩
  exact native_cube_alpha_bounded_tests D H (L ∘ f) _ M hM sigma hRat h
    (native_cube_local_to_alpha_haar D H (L ∘ f) _ M hM sigma hRat h hLf hlaw)

end Hindman168
