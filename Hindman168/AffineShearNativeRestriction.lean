import Hindman168.AffineShearNativeLift
import Hindman168.NativeLieSubalgebraNativeCoordinates

/-! Restrict the actual ambient automorphism to its invariant native Lie
subgroup.  Smoothness is proved using the existing genuine smooth retraction;
no smooth-restriction or derivative-compatibility certificate is assumed. -/
namespace Hindman168
open Function
open scoped Manifold ContDiff
universe u
attribute [local instance] lieGroup_smooth_min_three

noncomputable def affineShearRestrictGroupAut {G : Type*} [Group G]
    (H : Subgroup G) (φ : G ≃* G) (hH : H.map φ.toMonoidHom = H) : H ≃* H :=
  (φ.subgroupMap H).trans (MulEquiv.subgroupCongr hH)

 theorem affineShearRestrictGroupAut_val {G : Type*} [Group G]
    (H : Subgroup G) (φ : G ≃* G) (hH : H.map φ.toMonoidHom = H) (x : H) :
    (affineShearRestrictGroupAut H φ hH x).val = φ x.val := rfl

 theorem affineShear_native_restriction_mdifferentiable {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (φ : D.G ≃* D.G) (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hL : (nativeLieSubalgebraSubgroup (E := D.E) L).map φ.toMonoidHom =
      nativeLieSubalgebraSubgroup (E := D.E) L) :
    letI := nativeLieSubalgebraChartedSpace (E := D.E) L
    MDifferentiable 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L)
      𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L)
      (affineShearRestrictGroupAut (nativeLieSubalgebraSubgroup (E := D.E) L) φ hL) := by
  letI := nativeLieSubalgebraChartedSpace (E := D.E) L
  let ψ := affineShearRestrictGroupAut (nativeLieSubalgebraSubgroup (E := D.E) L) φ hL
  have h := ((nativeLieSubalgebraRetraction_contMDiff (E := D.E) L).mdifferentiable (by norm_num)).comp
    (hφ.comp ((nativeLieSubalgebra_inclusion_contMDiff (E := D.E) L).mdifferentiable (by norm_num)))
  have he : (ψ : nativeLieSubalgebraSubgroup (E := D.E) L →
      nativeLieSubalgebraSubgroup (E := D.E) L) =
      nativeLieSubalgebraRetraction (E := D.E) L ∘ φ ∘ Subtype.val := by
    funext x
    exact (nativeLieSubalgebraRetraction_left (E := D.E) L (ψ x)).symm
  change MDifferentiable _ _ (ψ : nativeLieSubalgebraSubgroup (E := D.E) L →
    nativeLieSubalgebraSubgroup (E := D.E) L)
  rw [he]
  exact h

 theorem affineShear_native_restriction_differential {s : ℕ}
    (D : NativeNilmanifoldData.{u} s) (L : LieSubalgebra ℝ (GroupLieAlgebra D.I D.G))
    (φ : D.G ≃* D.G) (hφ : MDifferentiable D.I D.I (φ : D.G → D.G))
    (hL : (nativeLieSubalgebraSubgroup (E := D.E) L).map φ.toMonoidHom =
      nativeLieSubalgebraSubgroup (E := D.E) L) :
    letI := nativeLieSubalgebraChartedSpace (E := D.E) L
    let J := 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L)
    ∀ v : nativeLieSubalgebraModel (E := D.E) L,
      (mfderiv J J
        (affineShearRestrictGroupAut (nativeLieSubalgebraSubgroup (E := D.E) L) φ hL) 1 v).val =
      affineShearNativeProjectionDifferential D D φ.toMonoidHom v.val := by
  letI := nativeLieSubalgebraChartedSpace (E := D.E) L
  letI := nativeLieSubalgebra_lieGroup L
  letI := nativeLieSubalgebra_boundaryless L
  let J := 𝓘(ℝ, nativeLieSubalgebraModel (E := D.E) L)
  let ψ := affineShearRestrictGroupAut (nativeLieSubalgebraSubgroup (E := D.E) L) φ hL
  dsimp only
  intro v
  apply nativeLieExponential_injective (I := D.I) (G := D.G)
  have he := congrArg Subtype.val
    (nativeLieExponential_map (I := J) (J := J) ψ.toMonoidHom
      (affineShear_native_restriction_mdifferentiable D L φ hφ hL) v)
  rw [nativeLieSubalgebra_native_exponential L, nativeLieSubalgebra_native_exponential L] at he
  change φ (nativeLieExponential (I := D.I) (G := D.G) v.val) =
    nativeLieExponential (I := D.I) (G := D.G) (mfderiv J J ψ 1 v).val at he
  exact he.symm.trans (nativeLieExponential_map φ.toMonoidHom hφ v.val)

end Hindman168
