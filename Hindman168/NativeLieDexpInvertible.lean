import Hindman168.NativeLieNilpotentDexp
import Hindman168.NilpotentPolynomialUnit
import Mathlib.Analysis.Normed.Operator.Banach

/-! The actual left-trivialized exponential differential is invertible
at every original model vector under original group nilpotency. This is
a local differential conclusion, not global exponential bijectivity. -/

namespace Hindman168
open Function Set Finset Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

 theorem nativeLieDexp_isUnit [Group.IsNilpotent G] (v : E) :
    IsUnit (nativeLieDexp (I := I) (G := G) v) := by
  rw [nativeLieDexp_finite_formula]
  apply nilpotent_polynomial_isUnit (nativeLieAdjointGenerator_pow_nilpotencyClass v)
  norm_num

 theorem nativeLieDexp_bijective [Group.IsNilpotent G] (v : E) :
    Bijective (nativeLieDexp (I := I) (G := G) v) :=
  ContinuousLinearMap.isUnit_iff_bijective.mp (nativeLieDexp_isUnit v)

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLeftTranslation_inv_comp (g : G) :
    let R : E →L[ℝ] E := mfderiv I I (fun x : G => g⁻¹ * x) g
    let L : E →L[ℝ] E := mfderiv I I (fun x : G => g * x) (1 : G)
    R.comp L = ContinuousLinearMap.id ℝ E := by
  have hl : MDifferentiableAt I I (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left : ContMDiff I I ∞ (fun x : G => g⁻¹ * x)).mdifferentiableAt (by norm_num)
  have hr : MDifferentiableAt I I (fun x : G => g * x) (1 : G) :=
    (contMDiff_mul_left : ContMDiff I I ∞ (fun x : G => g * x)).mdifferentiableAt (by norm_num)
  have he : (fun x : G => g⁻¹ * x) ∘ (fun x : G => g * x) = id := by
    funext x
    simp only [comp_apply, inv_mul_cancel_left, id_eq]
  apply ContinuousLinearMap.ext
  intro w
  have h := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := I) (1 : G) hl hr
    (by simp only [mul_one] : g * 1 = g) w
  rw [he, mfderiv_id] at h
  exact h.symm

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLeftTranslation_mfderiv_isUnit (g : G) :
    let L : E →L[ℝ] E := mfderiv I I (fun x : G => g * x) (1 : G)
    IsUnit L := by
  let L : E →L[ℝ] E := mfderiv I I (fun x : G => g * x) (1 : G)
  let R : E →L[ℝ] E := mfderiv I I (fun x : G => g⁻¹ * x) g
  change IsUnit L
  refine ⟨⟨L, R, ?_, ?_⟩, rfl⟩
  · convert! nativeLieLeftTranslation_comp_inv (I := I) g using 1
  · convert! nativeLieLeftTranslation_inv_comp (I := I) g using 1

 theorem nativeLieExponential_mfderiv_isUnit [Group.IsNilpotent G] (v : E) :
    let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
      (fun z : E => nativeLieExponential (I := I) (G := G) z) v
    IsUnit D := by
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
    (fun z : E => nativeLieExponential (I := I) (G := G) z) v
  let L : E →L[ℝ] E := mfderiv I I
    (fun x : G => nativeLieExponential (I := I) (G := G) v * x) (1 : G)
  change IsUnit D
  have hD : D = L * nativeLieDexp (I := I) (G := G) v :=
    nativeLieExponential_mfderiv_eq_leftTranslation_dexp v
  rw [hD]
  exact (nativeLieLeftTranslation_mfderiv_isUnit (I := I)
    (nativeLieExponential (I := I) (G := G) v)).mul (nativeLieDexp_isUnit v)

 theorem nativeLieExponential_mfderiv_bijective [Group.IsNilpotent G] (v : E) :
    let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
      (fun z : E => nativeLieExponential (I := I) (G := G) z) v
    Bijective D :=
  ContinuousLinearMap.isUnit_iff_bijective.mp (nativeLieExponential_mfderiv_isUnit v)

end Hindman168
