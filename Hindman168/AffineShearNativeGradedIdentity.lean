import Hindman168.AffineShearFaceAction
import Hindman168.AffineShearNativeLift
import Hindman168.NativeRationalCubeGroupIdentification
import Hindman168.LieExponentialHomomorphism

/-! Proposition 7.5's associated-graded identity from the actual native group
face action.  Exponential naturality and the proved identification of the
upper-face generated cube subgroup discharge Lie-cube preservation.  Neither
filtration preservation nor an associated-graded identity is assumed.

The input here is preservation on the group cover.  The separate lifting of a
quotient-coset symmetry to that cover is not asserted by this module. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] nativeFiniteProductTopologicalSpace nativeFiniteProductGroup
  nativeFiniteProductNormedAddCommGroup nativeFiniteProductNormedSpace
  nativeFiniteProductCompleteSpace nativeFiniteProductFiniteDimensional
  nativeFiniteProductT2Space nativeFiniteProductIsNilpotent nativeFiniteProductConnectedSpace
  nativeFiniteProductChartTopology nativeFiniteProductChartedSpace
  nativeFiniteProductLieGroup nativeFiniteProductBoundaryless lieGroup_smooth_min_three
  pointwiseLieRing pointwiseLieAlgebra nativeFiniteProductRationalModule
  nativeFiniteProduct_topologicalGroup

 theorem affineShear_native_cube_exp_mem_iff {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d))
    (z : Finset (Fin d) → GroupLieAlgebra D.I D.G) :
    (fun V => nativeLieExponential (I := D.I) (G := D.G) (z V)) ∈
      upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d ↔
      z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0 := by
  rw [← native_rational_cube_group_identification D F d n e]
  constructor
  · rintro ⟨g, hg, he⟩
    obtain ⟨x, hx⟩ := (native_rational_cube_subgroup_mem_iff D F d n e g).mp hg
    have hzx : z = x.val := by
      funext V
      apply nativeLieExponential_injective (I := D.I) (G := D.G)
      have hv := congrFun he V
      change nativeFiniteProductCoordinate n g (e.symm V) =
        nativeLieExponential (I := D.I) (G := D.G) (z V) at hv
      exact hv.symm.trans ((hx (e.symm V)).trans (by rw [e.apply_symm_apply]))
    rw [hzx]
    exact x.property
  · intro hz
    let x : nativeRationalCubeLieAlgebra D F d := ⟨z, hz⟩
    let g := nativeLieExponential (I := nativeFiniteProductCorners D.I n)
      (G := nativeFiniteProduct D.G n) (nativeRationalCubeLieEmbedding D F d n e x)
    refine ⟨g, ⟨nativeRationalCubeLieEmbedding D F d n e x, ⟨x, rfl⟩, rfl⟩, ?_⟩
    funext V
    change nativeFiniteProductCoordinate n g (e.symm V) = _
    exact (native_rational_cube_embedding_exponential D F d n e x (e.symm V)).trans
      (by rw [e.apply_symm_apply])

 theorem affineShear_native_face_differential_preserves_cube {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (d n : ℕ) (e : Fin (n+1) ≃ Finset (Fin d)) (j : Fin d)
    (c : D.G) (φ : D.G →* D.G)
    (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hface : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d,
      affineShearFaceAction j (fun y => c * φ y) z ∈
        upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d)
    (z : Finset (Fin d) → GroupLieAlgebra D.I D.G)
    (hz : z ∈ upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0) :
    affineShearFaceAction j (affineShearNativeProjectionDifferential D D φ) z ∈
      upperFaceLieLayer (L := GroupLieAlgebra D.I D.G) F.layer d 0 := by
  have hgroup := affineShearFaceAction_linearPart_mem
    (upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d) j c φ hface
    (fun V => nativeLieExponential (I := D.I) (G := D.G) (z V))
    ((affineShear_native_cube_exp_mem_iff D F d n e z).mpr hz)
  have he : affineShearFaceAction j φ
      (fun V => nativeLieExponential (I := D.I) (G := D.G) (z V)) =
      fun V => nativeLieExponential (I := D.I) (G := D.G)
        (affineShearFaceAction j (affineShearNativeProjectionDifferential D D φ) z V) := by
    classical
    funext V
    by_cases hj : j ∈ V
    · simp only [affineShearFaceAction, if_pos hj]
      exact nativeLieExponential_map φ hφ (z V)
    · simp only [affineShearFaceAction, if_neg hj]
  rw [he] at hgroup
  exact (affineShear_native_cube_exp_mem_iff D F d n e _).mp hgroup

 theorem affineShear_native_face_forces_graded_identity {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i n : ℕ) (e : Fin (n+1) ≃ Finset (Fin (i+1)))
    (c : D.G) (φ : D.G →* D.G)
    (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hface : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1),
      affineShearFaceAction (Fin.last i) (fun y => c * φ y) z ∈
        upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1))
    (x : D.E) (hx : x ∈ F.layer i) :
    affineShearNativeProjectionDifferential D D φ x - x ∈ F.layer (i+1) := by
  exact affineShearFaceAction_forces_graded_identity (L := GroupLieAlgebra D.I D.G)
    F.layer (affineShearNativeProjectionDifferential D D φ).toLinearMap i
    (affineShear_native_face_differential_preserves_cube D F (i+1) n e
      (Fin.last i) c φ hφ hface) x hx

 theorem affineShear_native_face_preserves_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i n : ℕ) (e : Fin (n+1) ≃ Finset (Fin (i+1)))
    (c : D.G) (φ : D.G →* D.G)
    (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hface : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1),
      affineShearFaceAction (Fin.last i) (fun y => c * φ y) z ∈
        upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1))
    (x : D.E) (hx : x ∈ F.layer i) :
    affineShearNativeProjectionDifferential D D φ x ∈ F.layer i := by
  have hd := affineShear_native_face_forces_graded_identity D F i n e c φ hφ hface x hx
  have hs := (F.layer i).add_mem (F.antitone (Nat.le_succ i) hd) hx
  simpa only [sub_add_cancel] using hs

/-- The linear part restricts to an automorphism of each actual subgroup
layer.  Surjectivity on the subgroup is proved from finite-dimensionality
and ambient injectivity, rather than assumed from quotient invariance. -/
 theorem affineShear_native_face_preserves_group_layer {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ)
    (i n : ℕ) (e : Fin (n+1) ≃ Finset (Fin (i+1)))
    (c : D.G) (φ : D.G →* D.G)
    (hφ : MDifferentiable D.I D.I (φ : D.G → D.G)) (hinj : Function.Injective φ)
    (hface : ∀ z ∈ upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1),
      affineShearFaceAction (Fin.last i) (fun y => c * φ y) z ∈
        upperFaceCubeGroup (nativeRationalSubgroupLayer D F) (i+1)) :
    (nativeRationalSubgroupLayer D F i).map φ = nativeRationalSubgroupLayer D F i := by
  let A := affineShearNativeProjectionDifferential D D φ
  have hA : Function.Injective A := affineShearNativeProjectionDifferential_injective D D φ hφ hinj
  have hpres : ∀ x ∈ F.layer i, A x ∈ F.layer i :=
    affineShear_native_face_preserves_layer D F i n e c φ hφ hface
  have hsur := affineShear_invariant_subspace_surjective A.toLinearMap hA (F.layer i) hpres
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    obtain ⟨v, hv, rfl⟩ := hg
    rw [nativeLieExponential_map φ hφ]
    exact native_rational_subgroup_layer_exp_mem D F i (hpres v hv)
  · intro g hg
    have hlog := (native_rational_subgroup_layer_logarithm_iff D F i g).mp hg
    obtain ⟨v, hv, he⟩ := hsur _ hlog
    refine ⟨nativeLieExponential (I := D.I) (G := D.G) v,
      native_rational_subgroup_layer_exp_mem D F i hv, ?_⟩
    exact (nativeLieExponential_map φ hφ v).trans
      ((congrArg (nativeLieExponential (I := D.I) (G := D.G)) he).trans
        (nativeLieExponential_globalLogarithm (I := D.I) g))

end Hindman168
