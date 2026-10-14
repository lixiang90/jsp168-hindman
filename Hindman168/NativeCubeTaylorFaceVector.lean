import Hindman168.NativeCubeFaceLevelCharacter
import Hindman168.NativeFiniteProductCoordinateLinear

/-! Actual internal cube face vectors, retaining the original filtration. -/
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

noncomputable def nativeCubeTaylorFaceVector {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ) (A : Finset (Fin d))
    (v : D.E) (hv : v ∈ F.layer k) : (nativeRationalCubeData D F d n e).E :=
  if hA : A.card ≤ k then
    nativeCubeLieModelMap D F d n e
      ⟨upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A v,
        upper_face_lie_layer_generator (L := GroupLieAlgebra D.I D.G) F.layer d 0 A v
          (by change v ∈ F.layer A.card; exact F.antitone hA hv)⟩
  else 0

theorem native_cube_taylor_face_vector_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ) (A : Finset (Fin d))
    (v : D.E) (hv : v ∈ F.layer k) :
    nativeCubeTaylorFaceVector D F d n e k A v hv ∈ nativeCubeInternalLayer D F d n e k := by
  classical
  unfold nativeCubeTaylorFaceVector
  split_ifs with hA
  · change nativeRationalCubeLieEmbedding D F d n e _ ∈ nativeCubeAmbientLayer D F d n e k
    refine ⟨upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A v, ?_, ?_⟩
    · apply upper_face_lie_layer_generator
      change v ∈ F.layer (max k A.card)
      rw [max_eq_left hA]
      exact hv
    · let x : nativeRationalCubeLieAlgebra D F d :=
        ⟨upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A v,
          upper_face_lie_layer_generator (L := GroupLieAlgebra D.I D.G) F.layer d 0 A v
            (by change v ∈ F.layer A.card; exact F.antitone hA hv)⟩
      exact native_cube_array_embedding_restrict D F d n e x
  · exact Submodule.zero_mem _

theorem native_cube_taylor_face_vector_coordinate {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ) (A : Finset (Fin d))
    (v : D.E) (hv : v ∈ F.layer k) (a : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeRationalCubeModelInclusion D F d n e
      (nativeCubeTaylorFaceVector D F d n e k A v hv)) a =
      if A.card ≤ k then (if A ⊆ e a then v else 0) else 0 := by
  classical
  by_cases hA : A.card ≤ k
  · rw [nativeCubeTaylorFaceVector, dif_pos hA, if_pos hA]
    let x : nativeRationalCubeLieAlgebra D F d :=
      ⟨upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A v,
        upper_face_lie_layer_generator (L := GroupLieAlgebra D.I D.G) F.layer d 0 A v
          (by change v ∈ F.layer A.card; exact F.antitone hA hv)⟩
    exact native_rational_cube_embedding_coordinate D F d n e x a
  · rw [nativeCubeTaylorFaceVector, dif_neg hA, if_neg hA, map_zero]
    exact (native_finite_product_coordinate_linear_apply n a 0).symm.trans
      (map_zero (nativeFiniteProductCoordinateLinear n a))

theorem native_cube_taylor_face_vector_functional {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (k : ℕ) (A : Finset (Fin d))
    (v : D.E) (hv : v ∈ F.layer k)
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ) :
    chi (nativeCubeTaylorFaceVector D F d n e k A v hv) =
      if A.card ≤ k then nativeCubeFaceFunctional D F d n e chi A v else 0 := by
  classical
  unfold nativeCubeTaylorFaceVector
  split_ifs with hA
  · exact (native_cube_array_functional_agrees D F d n e chi _).symm
  · exact map_zero chi

end Hindman168
