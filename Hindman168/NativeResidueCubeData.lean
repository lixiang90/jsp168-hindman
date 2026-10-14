import Hindman168.NativeCubeInternalFiltration
import Hindman168.NativeConjugateSubgroupFiltration
import Hindman168.NativeFiniteProductDiagonalLattice
import Hindman168.NativeRationalCubeGroupIdentification

/-! Actual rational-residue cube nilmanifolds. The SAME cube group and
filtration carry the diagonal-conjugated original product lattice.
The residue is not assumed to lie in the final subgroup or its cube. -/
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
attribute [local instance] nativeFiniteProductRationalModule nativeFiniteProduct_topologicalGroup
attribute [local instance] nativeFiniteProductModelTopology

noncomputable def nativeResidueCubeData {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : NativeNilmanifoldData.{u} s :=
  nativeRationalCubeData (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e

theorem native_residue_cube_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeResidueCubeData D F ρ hρ d n e).G = nativeRationalCubeSubgroup D F d n e := rfl

theorem native_residue_cube_lattice {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeResidueCubeData D F ρ hρ d n e).Γ =
      (roughConjugateSubgroup (nativeFiniteProductLattice D.Γ n)
        (nativeFiniteProductDiagonal ρ n)).comap (nativeRationalCubeSubgroup D F d n e).subtype := by
  change (nativeFiniteProductLattice (roughConjugateSubgroup D.Γ ρ) n).comap _ = _
  rw [native_finite_product_diagonal_lattice]
  rfl

noncomputable def nativeResidueCubeFiltration {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    NativeRationalLieFiltration (nativeResidueCubeData D F ρ hρ d n e) ℓ :=
  nativeCubeRationalLieFiltration (nativeConjugateNilmanifoldData D ρ)
    (nativeConjugateSubgroupFiltration D F ρ hρ) d n e

theorem native_residue_cube_filtration_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i : ℕ) :
    (nativeResidueCubeFiltration D F ρ hρ d n e).layer i = nativeCubeInternalLayer D F d n e i := rfl

theorem native_residue_cube_paper_group {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (nativeRationalCubeSubgroup (nativeConjugateNilmanifoldData D ρ)
      (nativeConjugateSubgroupFiltration D F ρ hρ) d n e).map (nativeCubeVertexHom d n e) =
      upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d :=
  native_rational_cube_group_identification D F d n e

end Hindman168
