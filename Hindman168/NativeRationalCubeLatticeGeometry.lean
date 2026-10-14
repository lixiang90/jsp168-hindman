import Hindman168.NativeRationalCubeSubgroup

/-! The actual cube exponential subgroup modulo the actual intersection
with the specified original product lattice is compact and metrizable. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three

attribute [local instance] pointwiseLieRing pointwiseLieAlgebra

attribute [local instance] nativeFiniteProductRationalModule


attribute [local instance] nativeFiniteProduct_topologicalGroup

theorem native_rational_cube_subgroup_rational {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
    nativeLatticeRationalSubspace (E := nativeFiniteProduct D.E n)
      (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n)
      (nativeLieSubalgebraModel (nativeRationalCubeNativeAlgebra D F d n e)) :=
  native_rational_cube_embedding_rational D F d n e

theorem native_rational_cube_lattice_discrete {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    DiscreteTopology ((nativeFiniteProductLattice D.Γ n).comap (nativeRationalCubeSubgroup D F d n e).subtype) := by
  letI := nativeFiniteProductLattice_discrete D.Γ n
  exact nativeLieLattice_intersection_discrete (nativeFiniteProductLattice D.Γ n) _

theorem native_rational_cube_lattice_compact {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    CompactSpace ((nativeRationalCubeSubgroup D F d n e) ⧸
      (nativeFiniteProductLattice D.Γ n).comap (nativeRationalCubeSubgroup D F d n e).subtype) := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  letI := nativeFiniteProductLattice_discrete D.Γ n
  letI := nativeFiniteProductLattice_cocompact D.Γ n
  exact nativeRationalLieLattice_quotient_compact (nativeFiniteProductLattice D.Γ n) _
    (native_rational_cube_subgroup_rational D F d n e)

theorem native_rational_cube_lattice_metrizable {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    TopologicalSpace.MetrizableSpace ((nativeRationalCubeSubgroup D F d n e) ⧸
      (nativeFiniteProductLattice D.Γ n).comap (nativeRationalCubeSubgroup D F d n e).subtype) := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  letI := nativeFiniteProductLattice_discrete D.Γ n
  letI := nativeFiniteProductLattice_cocompact D.Γ n
  exact nativeRationalLieLattice_quotient_metrizable (nativeFiniteProductLattice D.Γ n) _
    (native_rational_cube_subgroup_rational D F d n e)

end Hindman168
