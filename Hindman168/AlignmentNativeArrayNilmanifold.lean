import Hindman168.AlignmentNativeArrayLieGroup
import Hindman168.AlignmentNativeArrayCompact
import Hindman168.PointwiseArrayNilpotence
import Hindman168.NativeNilmanifoldConstruction

namespace Hindman168
open scoped Manifold ContDiff
universe v

attribute [local instance 10] nativeFiniteProductTopologicalSpace
attribute [local instance] nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

variable {σ E : Type v} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E] [Module ℚ E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type v} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [Group.IsNilpotent G]
  [ConnectedSpace G] [SimplyConnectedSpace G]

/-! The actual exponential array group and its exact pointwise lattice
now supply the existing native nilmanifold data, at the original step.
The quotient metric is constructed by the retained native constructor. -/

noncomputable def alignmentNativeArrayNilmanifold (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (s : ℕ) (hs : Group.nilpotencyClass G ≤ s)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] : NativeNilmanifoldData.{v} s := by
  let V := alignmentNativeFiniteImageModel (E := E) (I := I) (G := G) n u
  let A := alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu
  let L := pointwiseArrayLattice A Γ
  letI := alignmentNativeArrayChartedSpace (E := E) (I := I) (G := G) n u hu
  letI := alignmentNativeArray_lieGroup n u hu
  letI := alignmentNativeArray_boundaryless n u hu
  letI : IsTopologicalGroup A := topologicalGroup_of_lieGroup 𝓘(ℝ, V) ∞
  letI := alignmentNativeArrayGroup_contractible n u hu
  letI := alignmentNativeArrayGroup_simplyConnected n u hu
  letI := alignmentNativeArrayLattice_discrete n u hu Γ
  letI := alignmentNativeArrayLattice_quotient_compact n u hu Γ
  letI : Module ℚ V := Module.compHom _ (Rat.castHom ℝ)
  have hcut : (⊤ : Subgroup G).lowerCentralSeries s = ⊥ :=
    Subgroup.lowerCentralSeries_eq_bot_iff_nilpotencyClass_le.mpr hs
  letI := pointwiseArraySubgroup_nilpotent A s hcut
  exact nativeNilmanifoldOfLie (E := V) (I := 𝓘(ℝ, V)) (G := A) s
    (pointwiseArraySubgroup_nilpotencyClass_le A s hcut) L

theorem alignmentNativeArrayNilmanifold_group (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (s : ℕ) (hs : Group.nilpotencyClass G ≤ s)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (alignmentNativeArrayNilmanifold n u hu s hs Γ).G =
      alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu := rfl

theorem alignmentNativeArrayNilmanifold_lattice (n : ℕ)
    (u : Fin (n + 1) → σ → ℤ)
    (hu : Function.Injective (alignmentNativeFiniteEvaluation (E := E) (I := I) (G := G) n u))
    (s : ℕ) (hs : Group.nilpotencyClass G ≤ s)
    (Γ : Subgroup G) [DiscreteTopology Γ] [CompactSpace (G ⧸ Γ)] :
    (alignmentNativeArrayNilmanifold n u hu s hs Γ).Γ =
      pointwiseArrayLattice (alignmentNativeAllIntegerArrayGroup (E := E) (I := I) (G := G) n u hu) Γ := rfl

end Hindman168

