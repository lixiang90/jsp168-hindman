import Hindman168.AffineShearFilteredSection
import Hindman168.NativeNilmanifoldData
import Hindman168.LieExponentialHomomorphism

/-! The actual logarithmic affine map and its joint-cover lift.  The
right inverse is constructed from the given filtration, and the lift is a
bijection with the required exact group projection.  The separate strict
weighted polynomial-degree claim is intentionally not asserted here. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

@[reducible] noncomputable def affineShearNativeProjectionDifferential {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (π : D.G →* C.G) : D.E →L[ℝ] C.E :=
  mfderiv D.I C.I (π : D.G → C.G) 1

 theorem affineShearNativeProjectionDifferential_injective {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (π : D.G →* C.G) (hπ : MDifferentiable D.I C.I (π : D.G → C.G))
    (hinj : Function.Injective π) : Function.Injective (affineShearNativeProjectionDifferential D C π) := by
  intro x y hxy
  apply nativeLieExponential_injective (I := D.I) (G := D.G)
  apply hinj
  exact (nativeLieExponential_map π hπ x).trans
    ((congrArg (nativeLieExponential (I := C.I) (G := C.G)) hxy).trans
      (nativeLieExponential_map π hπ y).symm)

noncomputable def affineShearNativeLogEquiv {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (c : D.G) (φ : D.G ≃* D.G) : D.E ≃ D.E where
  toFun x := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
    (c * φ (nativeLieExponential (I := D.I) (G := D.G) x))
  invFun x := nativeLieGlobalLogarithm (E := D.E) (I := D.I) (G := D.G)
    (φ.symm (c⁻¹ * nativeLieExponential (I := D.I) (G := D.G) x))
  left_inv x := by
    simp only [nativeLieExponential_globalLogarithm, inv_mul_cancel_left,
      MulEquiv.symm_apply_apply, nativeLieGlobalLogarithm_exponential]
  right_inv x := by
    simp only [nativeLieExponential_globalLogarithm, MulEquiv.apply_symm_apply,
      mul_inv_cancel_left, nativeLieGlobalLogarithm_exponential]

 theorem affineShearNativeLogEquiv_exponential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (c : D.G) (φ : D.G ≃* D.G) (x : D.E) :
    nativeLieExponential (I := D.I) (G := D.G) (affineShearNativeLogEquiv D c φ x) =
      c * φ (nativeLieExponential (I := D.I) (G := D.G) x) :=
  nativeLieExponential_globalLogarithm (I := D.I) _

 theorem affineShear_native_joint_lift_projection {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (π : D.G →* C.G) (hπ : MDifferentiable D.I C.I (π : D.G → C.G))
    (R : C.E →ₗ[ℝ] D.E)
    (hR : (affineShearNativeProjectionDifferential D C π).toLinearMap.comp R = LinearMap.id)
    (c : C.G) (φ : C.G ≃* C.G) (u : D.E) :
    π (nativeLieExponential (I := D.I) (G := D.G)
      (affineShearSectionLiftEquiv (affineShearNativeProjectionDifferential D C π).toLinearMap
        R hR (affineShearNativeLogEquiv C c φ) u)) =
      c * φ (π (nativeLieExponential (I := D.I) (G := D.G) u)) := by
  let T := affineShearSectionLiftEquiv (affineShearNativeProjectionDifferential D C π).toLinearMap
    R hR (affineShearNativeLogEquiv C c φ)
  have hn (x : D.E) : π (nativeLieExponential (I := D.I) (G := D.G) x) =
      nativeLieExponential (I := C.I) (G := C.G) (affineShearNativeProjectionDifferential D C π x) :=
    nativeLieExponential_map π hπ x
  calc
    π (nativeLieExponential (I := D.I) (G := D.G) (T u)) =
        nativeLieExponential (I := C.I) (G := C.G)
          (affineShearNativeProjectionDifferential D C π (T u)) := hn (T u)
    _ = nativeLieExponential (I := C.I) (G := C.G)
        (affineShearNativeLogEquiv C c φ (affineShearNativeProjectionDifferential D C π u)) :=
      congrArg (nativeLieExponential (I := C.I) (G := C.G))
        (affineShearSectionLiftEquiv_projection _ R hR _ u)
    _ = c * φ (nativeLieExponential (I := C.I) (G := C.G)
        (affineShearNativeProjectionDifferential D C π u)) :=
      affineShearNativeLogEquiv_exponential C c φ _
    _ = c * φ (π (nativeLieExponential (I := D.I) (G := D.G) u)) :=
      congrArg (fun y => c * φ y) (hn u).symm

/-- The section and bijective lift both exist.  Surjectivity is required only
of the actual differential of the given group projection. -/
 theorem affineShear_native_filtered_joint_lift_exists {s t : ℕ}
    (D : NativeNilmanifoldData.{u} s) (C : NativeNilmanifoldData.{u} t)
    (π : D.G →* C.G) (hπ : MDifferentiable D.I C.I (π : D.G → C.G))
    (hp : Function.Surjective (affineShearNativeProjectionDifferential D C π))
    (ℓ : ℕ) (P : ℕ → Submodule ℝ D.E) (hP : Antitone P) (hterm : P (ℓ+1) = ⊥)
    (c : C.G) (φ : C.G ≃* C.G) :
    ∃ (R : C.E →ₗ[ℝ] D.E) (T : D.E ≃ D.E),
      (affineShearNativeProjectionDifferential D C π).toLinearMap.comp R = LinearMap.id ∧
      (∀ i, ((P i).map (affineShearNativeProjectionDifferential D C π).toLinearMap).map R ≤ P i) ∧
      (∀ u, T u = u + R (affineShearNativeLogEquiv C c φ
        (affineShearNativeProjectionDifferential D C π u) - affineShearNativeProjectionDifferential D C π u)) ∧
      ∀ u, π (nativeLieExponential (I := D.I) (G := D.G) (T u)) =
        c * φ (π (nativeLieExponential (I := D.I) (G := D.G) u)) := by
  obtain ⟨R, hR, hlevels⟩ := affineShear_terminal_filtered_section_exists
    (affineShearNativeProjectionDifferential D C π).toLinearMap hp ℓ P hP hterm
  refine ⟨R, affineShearSectionLiftEquiv
    (affineShearNativeProjectionDifferential D C π).toLinearMap R hR
      (affineShearNativeLogEquiv C c φ), hR, hlevels, (fun _ => rfl), ?_⟩
  exact affineShear_native_joint_lift_projection D C π hπ R hR c φ

end Hindman168
