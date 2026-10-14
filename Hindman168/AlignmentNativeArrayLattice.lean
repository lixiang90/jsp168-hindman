import Hindman168.AlignmentNativeArrayTopology
import Hindman168.FiniteDeterminedArrayLattice

namespace Hindman168
open scoped Manifold ContDiff

attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

theorem alignmentNativeArray_selected_injective (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u)) :
    Function.Injective (fun a : alignmentNativeAllIntegerArrayGroup
      (E := E) (I := I) (G := G) n u hu => fun i => a.val (u i)) := by
  intro a b hab
  apply (alignmentNativeArrayEquiv n u hu).symm.injective
  apply Subtype.ext
  apply nativeFiniteProductCoordinate_injective n
  funext i
  exact (alignmentNativeArrayEquiv_symm_coordinate n u hu a i).trans
    ((congrFun hab i).trans (alignmentNativeArrayEquiv_symm_coordinate n u hu b i).symm)

theorem alignmentNativeArrayLattice_discrete (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (Γ : Subgroup G) [DiscreteTopology Γ] :
    DiscreteTopology (pointwiseArrayLattice
      (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ) :=
  pointwiseArrayLattice_discrete _ Γ (n + 1) u
    (alignmentNativeArray_selected_injective n u hu)

end Hindman168

