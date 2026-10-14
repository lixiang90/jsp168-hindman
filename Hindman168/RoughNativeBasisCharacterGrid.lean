import Hindman168.RoughBasisFunctionalNorm
import Hindman168.RoughNativeHorizontalCharacterGrid

namespace Hindman168
open scoped BigOperators Manifold ContDiff

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] [Module ℚ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

theorem rough_native_basis_bounded_horizontal_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (b : Module.Basis ι ℝ E)
    (M : ℝ) (hM : 0 ≤ M) (χ : E →L[ℝ] ℝ) (hv : ∀ i, |χ (b i)| ≤ M)
    (hhor : RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ
      (roughBasisOperatorNormBudget b*M) :=
  rough_native_norm_bounded_horizontal_grid_mem Γ _
    (mul_nonneg (rough_basis_operator_norm_budget_positive b).le hM) χ
    (rough_basis_values_operator_norm b M hM χ hv) hhor

theorem rough_native_horizontal_integer_size_grid_mem (Γ : Subgroup G)
    [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] (b : Module.Basis ι ℝ E)
    (S : Finset ι) (hS : ∀ i, i ∉ S → b i ∈ nativeLieLowerCentralModel (I := I) (G := G) 1)
    (M : ℝ) (hM : 0 ≤ M) (χ : E →L[ℝ] ℝ)
    (hhor : RoughNativeHorizontalFunctional (E := E) (I := I) Γ χ.toLinearMap)
    (m : ι → ℤ) (hm : ∀ i ∈ S, χ (b i) = (m i : ℝ))
    (hsize : ∑ i ∈ S, (m i : ℝ)^2 ≤ M^2) :
    χ.toLinearMap ∈ roughNativeHorizontalCharacterGrid (E := E) (I := I) Γ
      (roughBasisOperatorNormBudget b*M) :=
  rough_native_basis_bounded_horizontal_grid_mem Γ b M hM χ
    (rough_basis_horizontal_integer_square_values_bound b S _ hS χ.toLinearMap hhor.2.1
      m hm M hM hsize) hhor

end Hindman168
