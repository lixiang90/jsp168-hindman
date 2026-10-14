import Hindman168.NativeRationalCubeLieImage
import Hindman168.NativeRationalLatticeCompact

/-! The cube algebra's exponential image is a genuine subgroup of the
original finite product, with exact original exponential vertex witnesses. -/
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


noncomputable def nativeRationalCubeNativeAlgebra {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    LieSubalgebra ℝ (GroupLieAlgebra (nativeFiniteProductCorners D.I n) (nativeFiniteProduct D.G n)) :=
  (nativeRationalCubeLieEmbedding D F d n e).range

theorem native_rational_cube_native_model {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    nativeLieSubalgebraModel (E := nativeFiniteProduct D.E n) (nativeRationalCubeNativeAlgebra D F d n e) =
      (nativeRationalCubeLieEmbedding D F d n e).toLinearMap.range := rfl

noncomputable def nativeRationalCubeSubgroup {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : Subgroup (nativeFiniteProduct D.G n) :=
  nativeLieSubalgebraSubgroup (E := nativeFiniteProduct D.E n) (nativeRationalCubeNativeAlgebra D F d n e)

theorem native_rational_cube_subgroup_mem_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (g : nativeFiniteProduct D.G n) :
    g ∈ nativeRationalCubeSubgroup D F d n e ↔
      ∃ x : nativeRationalCubeLieAlgebra D F d,
        ∀ k, nativeFiniteProductCoordinate n g k =
          nativeLieExponential (I := D.I) (G := D.G) (x.val (e k)) := by
  constructor
  · rintro ⟨v,⟨x,rfl⟩,rfl⟩
    exact ⟨x,fun k => native_rational_cube_embedding_exponential D F d n e x k⟩
  · rintro ⟨x,hx⟩
    refine ⟨nativeRationalCubeLieEmbedding D F d n e x,⟨x,rfl⟩,?_⟩
    apply nativeFiniteProductCoordinate_injective n
    funext k
    exact (native_rational_cube_embedding_exponential D F d n e x k).trans (hx k).symm

end Hindman168
