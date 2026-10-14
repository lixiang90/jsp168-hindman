import Hindman168.AffineShearNativeHomImage
import Hindman168.AffineShearCubeImage
import Hindman168.NativeRationalSubgroupFiltration

/-! The actual image filtration under a smooth lattice-compatible group
homomorphism.  Rationality, the bracket law, exact subgroup images and exact
full marginal cube images are theorems, not image-filtration certificates. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def affineShearNativeImageFiltration {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ) : NativeRationalSubgroupFiltration C ℓ where
  layer i := (F.layer i).map (affineShearNativeProjectionDifferential D C p).toLinearMap
  antitone := fun _ _ hij => Submodule.map_mono (F.antitone hij)
  initial := congrArg (Submodule.map (affineShearNativeProjectionDifferential D C p).toLinearMap) F.initial
  bracket := by
    rintro i j v w ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
    exact (affineShear_native_hom_bracket D C p hp a b) ▸
      (Submodule.mem_map_of_mem (F.bracket i j a b ha hb))
  rational i := affineShear_native_hom_rational_subspace D C p
    (hp.mdifferentiable (by norm_num)) hΓ (F.layer i) (F.rational i)
  terminal := by rw [F.terminal, Submodule.map_bot]

 theorem affineShear_native_image_layer {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ) (i : ℕ) :
    nativeRationalSubgroupLayer C (affineShearNativeImageFiltration D C F p hp hΓ) i =
      (nativeRationalSubgroupLayer D F i).map p := by
  ext g
  rw [native_rational_subgroup_layer_logarithm_iff]
  constructor
  · rintro ⟨v, hv, he⟩
    refine ⟨nativeLieExponential (I := D.I) (G := D.G) v,
      native_rational_subgroup_layer_exp_mem D F i hv, ?_⟩
    exact (nativeLieExponential_map p (hp.mdifferentiable (by norm_num)) v).trans
      ((congrArg (nativeLieExponential (I := C.I) (G := C.G)) he).trans
        (nativeLieExponential_globalLogarithm (I := C.I) g))
  · rintro ⟨a, ha, rfl⟩
    refine ⟨nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) a,
      (native_rational_subgroup_layer_logarithm_iff D F i a).mp ha, ?_⟩
    exact affineShear_native_hom_logarithm D C p (hp.mdifferentiable (by norm_num)) a

 theorem affineShear_native_cube_image {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ) (d : ℕ) :
    (upperFaceCubeGroup (nativeRationalSubgroupLayer D F) d).map (affineShearVertexMap d p) =
      upperFaceCubeGroup
        (nativeRationalSubgroupLayer C (affineShearNativeImageFiltration D C F p hp hΓ)) d := by
  rw [affineShear_cube_image]
  congr 1
  funext i
  exact (affineShear_native_image_layer D C F p hp hΓ i).symm

end Hindman168
