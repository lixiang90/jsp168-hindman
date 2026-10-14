import Hindman168.RoughNativeProductMvPolynomial
import Hindman168.RoughParametricWeightedPicard
import Hindman168.RoughNativeStretchedLieBracket

/-! Actual native polynomial multiplication preserves the SAME original
termwise Lie-filtration weights. No ordinary-degree multiplication bound
is substituted for the filtration degree needed by induction. -/

namespace Hindman168
open scoped Manifold ContDiff
variable {σ E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [Module ℚ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]
attribute [local instance] lieGroup_smooth_min_three

omit [Module ℚ E] in
theorem rough_native_product_polynomial_weighted (d : ℕ) (hd : 0 < d)
    {p q : RoughVectorMvPolynomial σ E} {k : ℕ}
    (hp : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) d) p k)
    (hq : RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) d) q k) :
    RoughVectorMvWeightedDegree (roughNativeStretchedLieFiltration (I := I) (G := G) d)
      (roughNativeProductMvPolynomial (I := I) (G := G) p q) k := by
  apply rough_parametric_weighted_endpoint
  exact rough_parametric_weighted_picard _ (rough_native_stretched_lie_antitone d hd) _
    (fun _ _ _ _ hv hw => rough_native_stretched_lie_bracket d hd hv hw) _ hq hp _

end Hindman168
