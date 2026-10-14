import Hindman168.NativeRationalCubeLieLayers
import Hindman168.NativeFiniteProductExponential
import Mathlib.Data.Fintype.Powerset

/-! The actual cube Lie algebra embeds into the native algebra of the
original finite product group, with exact vertex/exponential coordinates. -/
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

noncomputable def nativeCubeVertexEnumeration (d : ℕ) : Fin (2^d-1+1) ≃ Finset (Fin d) :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_finset, Fintype.card_fin]
    have hp : 0 < 2^d := pow_pos (by decide) d
    omega)).symm

noncomputable def nativeRationalCubeLieEmbedding {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    nativeRationalCubeLieAlgebra D F d →ₗ⁅ℝ⁆
      GroupLieAlgebra (nativeFiniteProductCorners D.I n) (nativeFiniteProduct D.G n) :=
  nativeFiniteProductLieMap n (fun k =>
    (pointwiseLieEvaluation ℝ _ (GroupLieAlgebra D.I D.G) (e k)).comp
      (nativeRationalCubeLieAlgebra D F d).incl)

theorem native_rational_cube_embedding_coordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (x : nativeRationalCubeLieAlgebra D F d) (k : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeLieEmbedding D F d n e x) k = x.val (e k) :=
  nativeFiniteProductLieMap_coordinate n _ x k

theorem native_rational_cube_embedding_injective {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    Function.Injective (nativeRationalCubeLieEmbedding D F d n e) := by
  intro x y hxy
  apply Subtype.ext
  funext V
  obtain ⟨k,rfl⟩ := e.surjective V
  have hk := congrArg (fun z => nativeFiniteProductCoordinate n z k) hxy
  exact (native_rational_cube_embedding_coordinate D F d n e x k).symm.trans
    (hk.trans (native_rational_cube_embedding_coordinate D F d n e y k))

theorem native_rational_cube_embedding_exponential {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (x : nativeRationalCubeLieAlgebra D F d) (k : Fin (n+1)) :
    nativeFiniteProductCoordinate n
      (nativeLieExponential (I := nativeFiniteProductCorners D.I n)
        (G := nativeFiniteProduct D.G n) (nativeRationalCubeLieEmbedding D F d n e x)) k =
      nativeLieExponential (I := D.I) (G := D.G) (x.val (e k)) :=
  nativeFiniteProductLieMap_exponential_coordinate n _ x k

end Hindman168
