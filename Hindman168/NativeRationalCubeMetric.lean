import Hindman168.NativeRationalCubeLatticeGeometry

/-! An actual compatible metric on the compact cube lattice quotient. -/
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

@[reducible]
noncomputable def nativeRationalCubeMetric {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    MetricSpace ((nativeRationalCubeSubgroup D F d n e) ⧸
      (nativeFiniteProductLattice D.Γ n).comap (nativeRationalCubeSubgroup D F d n e).subtype) := by
  letI := native_rational_cube_lattice_metrizable D F d n e
  exact TopologicalSpace.metrizableSpaceMetric _

theorem native_rational_cube_metric_topology {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeMetric D F d n e).toUniformSpace.toTopologicalSpace =
      QuotientGroup.instTopologicalSpace ((nativeFiniteProductLattice D.Γ n).comap
        (nativeRationalCubeSubgroup D F d n e).subtype) := by
  with_reducible_and_instances rfl

theorem native_rational_cube_metric_quotientMap {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    @IsOpenQuotientMap (nativeRationalCubeSubgroup D F d n e)
      ((nativeRationalCubeSubgroup D F d n e) ⧸ (nativeFiniteProductLattice D.Γ n).comap
        (nativeRationalCubeSubgroup D F d n e).subtype)
      inferInstance (nativeRationalCubeMetric D F d n e).toUniformSpace.toTopologicalSpace (↑) := by
  rw [native_rational_cube_metric_topology]
  exact QuotientGroup.isOpenQuotientMap_mk

end Hindman168
