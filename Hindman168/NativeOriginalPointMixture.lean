import Hindman168.NativeOriginalScaledPointMixture
import Hindman168.ComplexFloorWindowTransfer
import Hindman168.NativeSequentialOriginalLocalPointLaw

/-! The ORIGINAL q=0 point-mixture formula with the paper's floor(L)
sampling window and its actual mean denominator. -/
namespace Hindman168
open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology BigOperators
universe u
attribute [local instance] lieGroup_smooth_min_three

theorem native_original_point_mixture {s ℓ : ℕ}
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
      Tendsto (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L n⌋)
        (fun z => J (P n (z : ℝ) : D.G ⧸ D.Γ))) atTop
        (𝓝 (finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1,
          ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)))) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  intro J hJ
  exact complex_floor_window_limit L hL _ (fun _ _ => hJ.2 _) _
    (native_original_scaled_point_mixture D H L hL P M hM sigma hRat h hh hlaw J hJ)

theorem native_sequential_original_point_mixture {s ℓ : ℕ}
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
        ∀ J ∈ unitLipschitzObservables (D.G ⧸ D.Γ),
          Tendsto (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L (f n)⌋)
            (fun z => J (nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
              (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => (z : ℝ))) : D.G ⧸ D.Γ))) atTop
            (𝓝 (finiteComplexMean (fun r : Fin M => ∫ beta in (0 : ℝ)..1,
              ∫ y, J y ∂nativeRationalLayerHaarImage D H 0 (sigma r) (hRat r) (h beta)))) := by
  letI : MeasurableSpace D.G := borel D.G
  letI := D.metric
  letI : TopologicalSpace (D.G ⧸ D.Γ) := D.metric.toUniformSpace.toTopologicalSpace
  obtain ⟨f,hf,hLf,H,hHF,M,hM,sigma,hRat,h,hh,hlaw,hreal,_⟩ :=
    native_sequential_original_local_point_law D F L hL p hp
  refine ⟨f,hf,hLf,H,hHF,M,hM,sigma,hRat,h,hh,hlaw,hreal,?_⟩
  intro J hJ
  exact native_original_point_mixture D H (L ∘ f) hLf
    (fun n b => nativeLieExponential (E := D.E) (I := D.I) (G := D.G)
      (roughVectorMvEval (E := D.E) (p (f n)) (fun _ => b)))
    M hM sigma hRat h hh.continuous hlaw J hJ

end Hindman168
