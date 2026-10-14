import Hindman168.RoughNativeStretchedLieBracket
import Hindman168.RoughVectorWeightedDegree
import Hindman168.RoughNativeStretchedFiltration

namespace Hindman168
open scoped Manifold ContDiff

variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

omit [BoundarylessManifold I G] [T2Space G] in
theorem rough_native_weighted_polynomial_initial (D : ℕ) (hD : 0 < D)
    {p : RoughVectorMvPolynomial σ E} (hp : RoughVectorMvDegreeLE p D) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D) p 0 := by
  intro a ha
  rw [Nat.add_zero, rough_native_stretched_lie_initial D hD _ (hp a ha)]
  trivial

theorem rough_native_weighted_polynomial_bracket (D : ℕ) (hD : 0 < D)
    {p q : RoughVectorMvPolynomial σ E} {k l : ℕ}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D) p k)
    (hq : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D) q l) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D)
      (roughVectorMvBilinear (nativeLieAdjointDifferential (I := I) (G := G)) p q) (k+l) := by
  exact rough_vector_weighted_bilinear _ (rough_native_stretched_lie_antitone D hD) _
    (fun i j v w hv hw => rough_native_stretched_lie_bracket D hD hv hw) hp hq

theorem rough_native_weighted_polynomial_exp_mem [Module ℚ E] [Group.IsNilpotent G]
    [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]
    (D : ℕ) (hD : 0 < D) {p : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) D) p k)
    (x : σ → ℝ) : nativeLieExponential (I := I) (G := G) (roughVectorMvEval (E := E) p x) ∈
      roughStretchedLowerCentralFiltration G D k := by
  rw [rough_native_stretched_filtration_exp_mem_iff (I := I)]
  exact rough_vector_weighted_eval _ (rough_native_stretched_lie_antitone D hD) hp x

end Hindman168
