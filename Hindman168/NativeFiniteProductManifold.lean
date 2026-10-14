import Hindman168.NativeFiniteProductSpaces

/-! Actual iterated product charts and native Lie groups on the finite
product, with the original group at every factor. -/

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H]
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G]

def nativeFiniteProductChartModel (X : Type*) : ℕ → Type _
  | 0 => X
  | n + 1 => ModelProd (nativeFiniteProductChartModel X n) X

@[reducible]
def nativeFiniteProductChartTopology {X : Type*} [TopologicalSpace X] :
    (n : ℕ) → TopologicalSpace (nativeFiniteProductChartModel X n)
  | 0 => inferInstanceAs (TopologicalSpace X)
  | n + 1 => by
    letI := nativeFiniteProductChartTopology (X := X) n
    exact inferInstanceAs (TopologicalSpace (ModelProd (nativeFiniteProductChartModel X n) X))

attribute [local instance] nativeFiniteProductChartTopology

@[reducible]
def nativeFiniteProductChartedSpace :
    (n : ℕ) → ChartedSpace (nativeFiniteProductChartModel H n) (nativeFiniteProduct G n)
  | 0 => inferInstanceAs (ChartedSpace H G)
  | n + 1 => by
    letI := nativeFiniteProductChartedSpace n
    exact inferInstanceAs (ChartedSpace (ModelProd (nativeFiniteProductChartModel H n) H)
      (nativeFiniteProduct G n × G))

attribute [local instance] nativeFiniteProductChartedSpace

@[reducible]
noncomputable def nativeFiniteProductCorners (I : ModelWithCorners ℝ E H) :
    (n : ℕ) → ModelWithCorners ℝ (nativeFiniteProduct E n) (nativeFiniteProductChartModel H n)
  | 0 => I
  | n + 1 => (nativeFiniteProductCorners I n).prod I

variable {I : ModelWithCorners ℝ E H} [Group G] [LieGroup I ∞ G]

theorem nativeFiniteProductLieGroup :
    (n : ℕ) → LieGroup (nativeFiniteProductCorners I n) ∞ (nativeFiniteProduct G n)
  | 0 => inferInstanceAs (LieGroup I ∞ G)
  | n + 1 => by
    letI := nativeFiniteProductLieGroup n
    exact inferInstanceAs (LieGroup ((nativeFiniteProductCorners I n).prod I) ∞
      (nativeFiniteProduct G n × G))

omit [Group G] [LieGroup I ∞ G] in
theorem nativeFiniteProductBoundaryless [BoundarylessManifold I G] :
    (n : ℕ) → BoundarylessManifold (nativeFiniteProductCorners I n) (nativeFiniteProduct G n)
  | 0 => inferInstanceAs (BoundarylessManifold I G)
  | n + 1 => by
    letI := nativeFiniteProductBoundaryless n
    exact inferInstanceAs (BoundarylessManifold ((nativeFiniteProductCorners I n).prod I)
      (nativeFiniteProduct G n × G))

attribute [local instance] nativeFiniteProductLieGroup nativeFiniteProductBoundaryless

variable [CompleteSpace E] [FiniteDimensional ℝ E] [BoundarylessManifold I G]
  [T2Space G] [Group.IsNilpotent G] [ConnectedSpace G] [SimplyConnectedSpace G]

include I in
theorem nativeFiniteProductContractible :
    (n : ℕ) → ContractibleSpace (nativeFiniteProduct G n)
  | 0 => nativeLieGroup_contractible (I := I) (G := G)
  | n + 1 => by
    letI := nativeFiniteProductContractible n
    letI := nativeLieGroup_contractible (I := I) (G := G)
    exact inferInstanceAs (ContractibleSpace (nativeFiniteProduct G n × G))

include I in
theorem nativeFiniteProductSimplyConnected (n : ℕ) :
    SimplyConnectedSpace (nativeFiniteProduct G n) := by
  letI := nativeFiniteProductContractible (I := I) (G := G) n
  infer_instance

end Hindman168
