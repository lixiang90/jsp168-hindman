import Hindman168.NativeRationalCubeSubgroup
import Hindman168.NativeFiniteProductCoordinateHom
import Hindman168.NilUpperFaceGroup

/-! Every ORIGINAL filtered upper-face group generator belongs to the
actual exponential cube subgroup's vertex image. -/
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


theorem native_rational_cube_face_mem {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (A : Finset (Fin d))
    (g : D.G) (hg : g ∈ nativeRationalSubgroupLayer D F A.card) :
    upperFaceArray A g ∈ (nativeRationalCubeSubgroup D F d n e).map (nativeCubeVertexHom d n e) := by
  classical
  let v := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g
  have hv : v ∈ F.layer A.card := (native_rational_subgroup_layer_logarithm_iff D F A.card g).mp hg
  let x : nativeRationalCubeLieAlgebra D F d :=
    ⟨upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A v,
      upper_face_lie_layer_generator (L := GroupLieAlgebra D.I D.G) F.layer d 0 A v
        (by change v ∈ F.layer A.card; exact hv)⟩
  let z := nativeLieExponential (I := nativeFiniteProductCorners D.I n)
    (G := nativeFiniteProduct D.G n) (nativeRationalCubeLieEmbedding D F d n e x)
  refine ⟨z,⟨nativeRationalCubeLieEmbedding D F d n e x,⟨x,rfl⟩,rfl⟩,?_⟩
  funext V
  change nativeFiniteProductCoordinate n z (e.symm V) = upperFaceArray A g V
  have he := native_rational_cube_embedding_exponential D F d n e x (e.symm V)
  apply he.trans
  rw [e.apply_symm_apply]
  change nativeLieExponential (I := D.I) (G := D.G) (if A ⊆ V then v else 0) =
    (if A ⊆ V then g else 1)
  by_cases hA : A ⊆ V
  · simp only [if_pos hA]
    exact nativeLieExponential_globalLogarithm (E := D.E) (I := D.I) (G := D.G) g
  · simp only [if_neg hA]
    exact nativeLieExponential_zero (I := D.I) (G := D.G)

theorem native_rational_upper_face_group_le {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d ≤
      (nativeRationalCubeSubgroup D F d n e).map (nativeCubeVertexHom d n e) := by
  apply (Subgroup.closure_le (K :=
    (nativeRationalCubeSubgroup D F d n e).map (nativeCubeVertexHom d n e))).mpr
  rintro _ ⟨A,g,hg,rfl⟩
  exact native_rational_cube_face_mem D F d n e A g hg

end Hindman168
