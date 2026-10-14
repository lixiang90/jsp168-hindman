import Hindman168.NativeProductExponential
import Hindman168.NativeLieGlobalTopology

/-! Global native logarithms of the original simply connected nilpotent
groups are compatible with their actual product. -/

namespace Hindman168
open scoped Manifold ContDiff

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  {G K : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  [Group K] [TopologicalSpace K] [ChartedSpace H' K]
  [LieGroup I ∞ G] [LieGroup J ∞ K] [BoundarylessManifold I G]
  [BoundarylessManifold J K] [T2Space G] [T2Space K]
  [Group.IsNilpotent G] [Group.IsNilpotent K]
  [ConnectedSpace G] [SimplyConnectedSpace G]
  [ConnectedSpace K] [SimplyConnectedSpace K]

attribute [local instance] lieGroup_smooth_min_three

include I J in
theorem nativeProductGroup_contractible : ContractibleSpace (G × K) := by
  letI : ContractibleSpace G := nativeLieGroup_contractible (I := I) (G := G)
  letI : ContractibleSpace K := nativeLieGroup_contractible (I := J) (G := K)
  infer_instance

include I J in
theorem nativeProductGroup_simplyConnected : SimplyConnectedSpace (G × K) := by
  letI := nativeProductGroup_contractible (I := I) (J := J) (G := G) (K := K)
  infer_instance

theorem nativeProductGlobalLogarithm_eq (g : G × K) :
    letI := nativeProductGroup_simplyConnected (I := I) (J := J) (G := G) (K := K)
    nativeLieGlobalLogarithm (I := I.prod J) (G := G × K) g =
      (nativeLieGlobalLogarithm (I := I) (G := G) g.1,
        nativeLieGlobalLogarithm (I := J) (G := K) g.2) := by
  letI := nativeProductGroup_simplyConnected (I := I) (J := J) (G := G) (K := K)
  apply nativeLieExponential_injective (I := I.prod J) (G := G × K)
  exact (nativeLieExponential_globalLogarithm (I := I.prod J) (G := G × K) g).trans
    ((nativeProductExponential_eq (I := I) (J := J) (G := G) (K := K)
      (nativeLieGlobalLogarithm (I := I) (G := G) g.1,
        nativeLieGlobalLogarithm (I := J) (G := K) g.2)).trans
      (Prod.ext (nativeLieExponential_globalLogarithm (I := I) (G := G) g.1)
        (nativeLieExponential_globalLogarithm (I := J) (G := K) g.2))).symm

end Hindman168
