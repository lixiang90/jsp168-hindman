import Hindman168.AffineShearNativeLift
import Hindman168.NativeLatticeRationalCoordinates
import Hindman168.NativeSmoothHomLieBracket
import Hindman168.RationalRealSpanTransport

/-! Images under genuine smooth lattice-compatible homomorphisms preserve
native logarithms, rational Lie subspaces and the genuine native bracket.
These statements use the actual identity differential, not a supplied Lie map. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

 theorem affineShear_native_hom_logarithm {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (p : D.G →* C.G) (hp : MDifferentiable D.I C.I (p : D.G → C.G)) (g : D.G) :
    affineShearNativeProjectionDifferential D C p
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) =
      nativeLieGlobalLogarithm (E := C.E) (I := C.I) (G := C.G) (p g) := by
  apply nativeLieExponential_injective (I := C.I) (G := C.G)
  exact (nativeLieExponential_map p hp _).symm.trans
    ((congrArg p (nativeLieExponential_globalLogarithm (I := D.I) g)).trans
      (nativeLieExponential_globalLogarithm (I := C.I) (p g)).symm)

 theorem affineShear_native_hom_rational_span {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (p : D.G →* C.G) (hp : MDifferentiable D.I C.I (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ) {v : D.E}
    (hv : v ∈ nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ) :
    affineShearNativeProjectionDifferential D C p v ∈
      nativeSubgroupRationalLogSpan (E := C.E) (I := C.I) C.Γ := by
  let A := (affineShearNativeProjectionDifferential D C p).toLinearMap.restrictScalars ℚ
  have hle : nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ ≤
      (nativeSubgroupRationalLogSpan (E := C.E) (I := C.I) C.Γ).comap A := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, hg, rfl⟩
    change affineShearNativeProjectionDifferential D C p
      (nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G) g) ∈
        nativeSubgroupRationalLogSpan (E := C.E) (I := C.I) C.Γ
    rw [affineShear_native_hom_logarithm D C p hp]
    exact nativeSubgroup_logarithm_mem_span C.Γ (hΓ g hg)
  exact hle hv

 theorem affineShear_native_hom_rational_subspace {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (p : D.G →* C.G) (hp : MDifferentiable D.I C.I (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ) (V : Submodule ℝ D.E)
    (hV : nativeLatticeRationalSubspace (E := D.E) (I := D.I) D.Γ V) :
    nativeLatticeRationalSubspace (E := C.E) (I := C.I) C.Γ
      (V.map (affineShearNativeProjectionDifferential D C p).toLinearMap) :=
  rational_real_span_map (affineShearNativeProjectionDifferential D C p).toLinearMap V
    (nativeSubgroupRationalLogSpan (E := D.E) (I := D.I) D.Γ)
    (nativeSubgroupRationalLogSpan (E := C.E) (I := C.I) C.Γ)
    (fun _ hv => affineShear_native_hom_rational_span D C p hp hΓ hv) hV

 theorem affineShear_native_hom_bracket {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (p : D.G →* C.G) (hp : ContMDiff D.I C.I ∞ (p : D.G → C.G)) (v w : D.E) :
    affineShearNativeProjectionDifferential D C p
      (nativeLieAdjointDifferential (I := D.I) (G := D.G) v w) =
      nativeLieAdjointDifferential (I := C.I) (G := C.G)
        (affineShearNativeProjectionDifferential D C p v)
        (affineShearNativeProjectionDifferential D C p w) := by
  simpa only [nativeLieAdjointGenerator_eq_differential] using
    nativeSmoothHom_generator_intertwine p hp v w

 theorem affineShear_native_hom_rational_hull {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (p : D.G →* C.G) (hp : MDifferentiable D.I C.I (p : D.G → C.G))
    (hΓ : ∀ g ∈ D.Γ, p g ∈ C.Γ) {ρ : D.G}
    (hρ : ρ ∈ nativeSubgroupRationalHull (E := D.E) (I := D.I) D.Γ) :
    p ρ ∈ nativeSubgroupRationalHull (E := C.E) (I := C.I) C.Γ := by
  apply (nativeSubgroupRationalHull_mem_iff C.Γ (p ρ)).mpr
  rw [← affineShear_native_hom_logarithm D C p hp]
  exact affineShear_native_hom_rational_span D C p hp hΓ
    ((nativeSubgroupRationalHull_mem_iff D.Γ ρ).mp hρ)

end Hindman168
