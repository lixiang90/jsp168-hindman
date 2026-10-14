import Hindman168.AffineShearNativeInitialLayer
import Hindman168.AffineShearNativeImageFiltration

/-! The actual projection between the proper level-one native models is
surjective and has exactly the image filtration.  These are proved from the
original ambient group homomorphism, without a supplied section or model map. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

 theorem affineShear_layer_le_initial {s ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (F : NativeRationalSubgroupFiltration D ℓ) (i : ℕ) :
    F.layer i ≤ F.layer 1 := by
  cases i with
  | zero => exact le_of_eq F.initial
  | succ i => exact F.antitone (Nat.succ_le_succ (Nat.zero_le i))

noncomputable def affineShearNativeInitialProjection {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    (nativeRationalLayerOrbitData D F 1 ρ hρ).E →ₗ[ℝ]
      (nativeRationalLayerOrbitData C (affineShearNativeImageFiltration D C F p hp hΓ) 1
        (p ρ) (affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ)).E where
  toFun v := ⟨affineShearNativeProjectionDifferential D C p v.val, ⟨v.val, v.property, rfl⟩⟩
  map_add' v w := Subtype.ext (map_add (affineShearNativeProjectionDifferential D C p) v.val w.val)
  map_smul' r v := Subtype.ext (map_smul (affineShearNativeProjectionDifferential D C p) r v.val)

 theorem affineShear_native_initial_projection_surjective {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    Function.Surjective (affineShearNativeInitialProjection D C F p hp hΓ ρ hρ) := by
  intro y
  obtain ⟨v, hv, he⟩ := y.property
  exact ⟨⟨v, hv⟩, Subtype.ext he⟩

 theorem affineShear_native_initial_projection_layers {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) (i : ℕ) :
    (affineShearNativeInitialFiltration D F ρ hρ i).map
        (affineShearNativeInitialProjection D C F p hp hΓ ρ hρ) =
      affineShearNativeInitialFiltration C (affineShearNativeImageFiltration D C F p hp hΓ)
        (p ρ) (affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ) i := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v.val, hv, rfl⟩
  · intro hy
    obtain ⟨v, hv, he⟩ := hy
    exact ⟨⟨v, affineShear_layer_le_initial D F i hv⟩, hv, Subtype.ext he⟩

 theorem affineShear_native_initial_projection_exponential {s t ℓ : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (F : NativeRationalSubgroupFiltration D ℓ)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ)
    (ρ : D.G) (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    let K := nativeRationalLayerOrbitData D F 1 ρ hρ
    let J := nativeRationalLayerOrbitData C (affineShearNativeImageFiltration D C F p hp hΓ) 1
      (p ρ) (affineShear_native_hom_rational_hull D C p (hp.mdifferentiable (by norm_num)) hΓ hρ)
    ∀ v : K.E, p (nativeLieExponential (I := K.I) (G := K.G) v).val =
      (nativeLieExponential (I := J.I) (G := J.G)
        (affineShearNativeInitialProjection D C F p hp hΓ ρ hρ v)).val := by
  dsimp only
  intro v
  have hu := congrArg Subtype.val
    (nativeLieSubalgebra_native_exponential (nativeRationalSubgroupLayerAlgebra D F 1) v)
  have hv := congrArg Subtype.val
    (nativeLieSubalgebra_native_exponential
      (nativeRationalSubgroupLayerAlgebra C (affineShearNativeImageFiltration D C F p hp hΓ) 1)
      (affineShearNativeInitialProjection D C F p hp hΓ ρ hρ v))
  exact (congrArg p hu).trans
    ((nativeLieExponential_map p (hp.mdifferentiable (by norm_num)) v.val).trans hv.symm)

end Hindman168
