import Hindman168.NativeLieSubalgebraTopology

/-! The existing original global exponential/logarithm give a genuine
homeomorphism of the entire native group with its real vector model. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [FiniteDimensional ℝ E] [ConnectedSpace G] [SimplyConnectedSpace G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieGlobalExponentialHomeomorph : E ≃ₜ G where
  toFun := nativeLieExponential (I := I) (G := G)
  invFun := nativeLieGlobalLogarithm (E := E) (I := I) (G := G)
  left_inv := nativeLieGlobalLogarithm_exponential (I := I) (G := G)
  right_inv := nativeLieExponential_globalLogarithm (I := I) (G := G)
  continuous_toFun := nativeLieExponential_continuous (I := I) (G := G)
  continuous_invFun := (nativeLieGlobalLogarithm (E := E) (I := I) (G := G)).continuous

include I in
theorem nativeLieGroup_contractible : ContractibleSpace G :=
  (nativeLieGlobalExponentialHomeomorph (E := E) (I := I) (G := G)).symm.contractibleSpace

end Hindman168
