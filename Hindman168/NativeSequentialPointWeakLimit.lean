import Hindman168.NativeOriginalPointWeakLimit

/-! ONE original factorization subsequence, retaining both local laws and
its actual weak probability point-mixture limit. -/
namespace Hindman168
open Filter MeasureTheory
open scoped Manifold ContDiff Topology
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_sequential_original_point_weak_limit {s ℓ : ℕ}
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
        Tendsto (fun n => finiteEmpiricalProbability (Finset.Ico 0 ⌊L (f n)⌋)
          (fun z => (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
            (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => (z : ℝ))) : D.G ⧸ D.Γ))
          (1 : D.G)) atTop
          (𝓝 (nativePointMixtureProbability D H M hM sigma hRat h hh.continuous)) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨f,hf,hLf,H,hHF,M,hM,sigma,hRat,h,hh,hlaw,hreal,_⟩ :=
    native_sequential_original_local_point_law D F L hL p hp
  refine ⟨f,hf,hLf,H,hHF,M,hM,sigma,hRat,h,hh,hlaw,hreal,?_⟩
  exact native_original_point_weak_limit D H (L ∘ f) hLf
    (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)))
    M hM sigma hRat h hh.continuous hlaw

end Hindman168
