import Hindman168.NativeCubeHorizontalArray
import Hindman168.UpperFaceCharacterMaximal
import Hindman168.NativeSubgroupLevelCharacters

/-! A genuine horizontal obstruction on the actual cube produces a
nonzero ORIGINAL rational level character at the greatest surviving face
level. All bracket and rationality conditions are derived. -/
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

noncomputable def nativeCubeFaceFunctional {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ) (A : Finset (Fin d)) : D.E →ₗ[ℝ] ℝ :=
  (nativeCubeArrayFunctional D F d n e chi).comp
    (upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A).toLinearMap

theorem native_cube_horizontal_face_maximal_level {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (chi : (nativeRationalCubeData D F d n e).E →ₗ[ℝ] ℝ)
    (hChi : RoughNativeHorizontalFunctional (I := (nativeRationalCubeData D F d n e).I)
      (nativeRationalCubeData D F d n e).Γ chi) :
    ∃ j : ℕ, 1 ≤ j ∧ j ≤ ℓ ∧ ∃ A : Finset (Fin d), A.card ≤ j ∧
      NativeSubgroupRationalLevelCharacter D F j (nativeCubeFaceFunctional D F d n e chi A) ∧
      ∀ k : ℕ, j < k → ∀ B : Finset (Fin d), B.card ≤ k →
        F.layer k ≤ (nativeCubeFaceFunctional D F d n e chi B).ker := by
  classical
  let c := nativeCubeArrayFunctional D F d n e chi
  have hNonzero := native_cube_array_functional_nonzero D F d n e chi hChi.1
  obtain ⟨j,hj,hjTop,⟨A,hA,v,hv,hv0⟩,hTail⟩ :=
    upper_face_character_maximal_level (L := GroupLieAlgebra D.I D.G)
      F.layer F.antitone F.initial ℓ d F.terminal c hNonzero
  refine ⟨j,hj,hjTop,A,hA,?_,fun k hk B hB x hx => hTail k hk B hB x hx⟩
  refine ⟨⟨v,hv,hv0⟩,?_,?_,?_⟩
  · intro x hx
    exact hTail (j+1) (by omega) A (by omega) x hx
  · intro a b _ _ hab x hx y hy
    have hb := upper_face_character_bracket (L := GroupLieAlgebra D.I D.G)
      F.layer F.antitone d c (native_cube_horizontal_array_bracket D F d n e chi hChi)
      A a b (by omega) x y hx hy
    have he := (nativeLieAdjointGenerator_eq_native_bracket (I := D.I) (G := D.G) x y).symm.trans
        (DFunLike.congr_fun (nativeLieAdjointGenerator_eq_differential (I := D.I) (G := D.G) x) y)
    exact (congrArg (fun t : GroupLieAlgebra D.I D.G => c (upperFaceLieArray (R := ℝ) A t)) he).symm.trans hb
  · intro x hx hxRat
    let z : nativeRationalCubeLieAlgebra D F d :=
      ⟨upperFaceLieArray (R := ℝ) (L := GroupLieAlgebra D.I D.G) A x,
        upper_face_lie_layer_generator (L := GroupLieAlgebra D.I D.G) F.layer d 0 A x
          (by change x ∈ F.layer A.card; exact F.antitone hA hx)⟩
    apply native_cube_horizontal_array_rational D F d n e chi hChi z
    intro V
    change (if A ⊆ V then x else 0) ∈ _
    split_ifs
    · exact hxRat
    · exact Submodule.zero_mem _

end Hindman168
