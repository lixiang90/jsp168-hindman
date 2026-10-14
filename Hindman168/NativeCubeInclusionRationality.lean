import Hindman168.NativeRationalCubeInclusion

/-! Rational logarithms in the internal cube are exactly the rational
ambient logarithms under the ACTUAL lattice inclusion. -/
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

attribute [local instance] nativeFiniteProductModelTopology

theorem native_cube_inclusion_rational_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (v : (nativeRationalCubeData D F d n e).E) :
    letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
    v ∈ nativeSubgroupRationalLogSpan (E := (nativeRationalCubeData D F d n e).E)
      (I := (nativeRationalCubeData D F d n e).I) (nativeRationalCubeData D F d n e).Γ ↔
    nativeRationalCubeModelInclusion D F d n e v ∈
      nativeSubgroupRationalLogSpan (E := nativeFiniteProduct D.E n)
        (I := nativeFiniteProductCorners D.I n) (nativeFiniteProductLattice D.Γ n) := by
  letI := nativeFiniteProductSimplyConnected (I := D.I) (G := D.G) n
  rw [nativeSubgroupRationalLogSpan_mem_iff_positive_power,
    nativeSubgroupRationalLogSpan_mem_iff_positive_power]
  have he := native_rational_cube_data_exponential D F d n e v
  apply exists_congr
  intro k
  apply and_congr_right
  intro _
  change nativeRationalCubeGroupInclusion D F d n e
    (nativeLieExponential (I := (nativeRationalCubeData D F d n e).I)
      (G := (nativeRationalCubeData D F d n e).G) v ^ k) ∈ nativeFiniteProductLattice D.Γ n ↔ _
  rw [map_pow,he]

end Hindman168
