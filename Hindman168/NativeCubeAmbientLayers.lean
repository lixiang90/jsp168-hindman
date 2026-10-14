import Hindman168.NativeRationalCubeSubgroup

/-! The paper max(i,|face|) layers as actual subspaces in the native
finite-product model, using exact vertex evaluations. -/
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

noncomputable def nativeCubeArrayEmbedding {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    (Finset (Fin d) → GroupLieAlgebra D.I D.G) →ₗ⁅ℝ⁆
      GroupLieAlgebra (nativeFiniteProductCorners D.I n) (nativeFiniteProduct D.G n) :=
  nativeFiniteProductLieMap n (fun k => pointwiseLieEvaluation ℝ _ (GroupLieAlgebra D.I D.G) (e k))

theorem native_cube_array_embedding_coordinate {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (x : Finset (Fin d) → GroupLieAlgebra D.I D.G) (k : Fin (n+1)) :
    nativeFiniteProductCoordinate n (nativeCubeArrayEmbedding D d n e x) k = x (e k) :=
  nativeFiniteProductLieMap_coordinate n _ x k

theorem native_cube_array_embedding_restrict {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (x : nativeRationalCubeLieAlgebra D F d) :
    nativeCubeArrayEmbedding D d n e x.val = nativeRationalCubeLieEmbedding D F d n e x := by
  apply nativeFiniteProductCoordinate_injective n
  funext k
  exact (native_cube_array_embedding_coordinate D d n e x.val k).trans
    (native_rational_cube_embedding_coordinate D F d n e x k).symm

noncomputable def nativeCubeAmbientLayer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i : ℕ) : Submodule ℝ (nativeFiniteProduct D.E n) :=
  (upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d i).map
    (nativeCubeArrayEmbedding D d n e).toLinearMap

theorem native_cube_ambient_antitone {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : Antitone (nativeCubeAmbientLayer D F d n e) := by
  intro i j hij
  exact Submodule.map_mono (upper_face_lie_layer_antitone (L := GroupLieAlgebra D.I D.G) F.layer F.antitone d hij)

theorem native_cube_ambient_initial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    nativeCubeAmbientLayer D F d n e 0 = nativeCubeAmbientLayer D F d n e 1 := by
  exact congrArg (fun P => P.map (nativeCubeArrayEmbedding D d n e).toLinearMap)
    (upper_face_lie_layer_initial (L := GroupLieAlgebra D.I D.G) F.layer F.initial d)

theorem native_cube_ambient_zero {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) :
    nativeCubeAmbientLayer D F d n e 0 = nativeLieSubalgebraModel
      (E := nativeFiniteProduct D.E n) (nativeRationalCubeNativeAlgebra D F d n e) := by
  apply le_antisymm
  · rintro y ⟨x,hx,rfl⟩
    exact ⟨⟨x,hx⟩,(native_cube_array_embedding_restrict D F d n e ⟨x,hx⟩).symm⟩
  · rintro y ⟨x,rfl⟩
    exact ⟨x.val,x.property,native_cube_array_embedding_restrict D F d n e x⟩

theorem native_cube_ambient_terminal {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) : nativeCubeAmbientLayer D F d n e (ℓ+1) = ⊥ := by
  change (upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d (ℓ+1)).map _ = _
  exact (congrArg (fun P => P.map (nativeCubeArrayEmbedding D d n e).toLinearMap)
    (upper_face_lie_layer_terminal (L := GroupLieAlgebra D.I D.G) F.layer F.antitone d (ℓ+1) F.terminal)).trans
      (Submodule.map_bot _)

theorem native_cube_ambient_bracket {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (i j : ℕ)
    (v w : nativeFiniteProduct D.E n) (hv : v ∈ nativeCubeAmbientLayer D F d n e i)
    (hw : w ∈ nativeCubeAmbientLayer D F d n e j) :
    nativeLieAdjointDifferential (I := nativeFiniteProductCorners D.I n)
      (G := nativeFiniteProduct D.G n) v w ∈ nativeCubeAmbientLayer D F d n e (i+j) := by
  obtain ⟨x,hx,rfl⟩ := hv
  obtain ⟨y,hy,rfl⟩ := hw
  have hb : ⁅x,y⁆ ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d (i+j) :=
    native_rational_cube_lie_layer_bracket D F d i j hx hy
  refine ⟨⁅x,y⁆,hb,?_⟩
  have he := (nativeCubeArrayEmbedding D d n e).map_lie x y
  exact he.trans ((nativeLieAdjointGenerator_eq_native_bracket
    (I := nativeFiniteProductCorners D.I n) (G := nativeFiniteProduct D.G n) _ _).symm.trans
      (DFunLike.congr_fun (nativeLieAdjointGenerator_eq_differential
        (I := nativeFiniteProductCorners D.I n) (G := nativeFiniteProduct D.G n) _) _))

end Hindman168
