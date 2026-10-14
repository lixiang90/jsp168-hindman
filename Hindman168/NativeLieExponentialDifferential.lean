import Hindman168.NativeLieParameterJacobianCocycle

/-! The actual relative parameter derivative at time one is precisely
the left trivialization of the original native exponential differential.
It is identified using only actual manifold chain rules. -/

namespace Hindman168
open Function Set Filter Topology
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G]

attribute [local instance] lieGroup_smooth_min_three

noncomputable def nativeLieDexp (v : E) : E →L[ℝ] E :=
  (mfderiv I I (fun x : G => (nativeLieExponential (I := I) (G := G) v)⁻¹ * x)
    (nativeLieExponential (I := I) (G := G) v)).comp
      (mfderiv 𝓘(ℝ, E) I (fun z : E => nativeLieExponential (I := I) (G := G) z) v)

 theorem nativeLieRelativeCurve_time_one (v w : E) :
    nativeLieRelativeCurve (I := I) (G := G) v (1, w) =
      (nativeLieExponential (I := I) (G := G) v)⁻¹ *
        nativeLieExponential (I := I) (G := G) (v + w) := by
  simp only [nativeLieRelativeCurve, lieOneParameterCurve_neg_eq_inv, nativeLieExponential]

 theorem nativeLieDexp_eq_parameterJacobian (v : E) :
    nativeLieDexp (I := I) (G := G) v =
      nativeLieCurveParameterJacobian (I := I) (G := G) v 1 := by
  let exp : E → G := nativeLieExponential (I := I) (G := G)
  let S : E → E := fun w => v + w
  let f : E → G := exp ∘ S
  let L : G → G := fun x => (exp v)⁻¹ * x
  have hs : HasMFDerivAt 𝓘(ℝ, E) 𝓘(ℝ, E) (fun w : E => v + w) 0
      (ContinuousLinearMap.id ℝ E) := by
    convert! ((hasFDerivAt_const v (0 : E)).add (hasFDerivAt_id (𝕜 := ℝ) (0 : E))).hasMFDerivAt using 1
    simp only [zero_add]
  have hS : (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) S 0 : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := by
    convert! hs.mfderiv using 1
  have hS0 : S 0 = v := add_zero v
  have hexp : MDifferentiableAt 𝓘(ℝ, E) I exp v :=
    (nativeLieExponential_contMDiff (I := I) (G := G)).mdifferentiableAt (by norm_num)
  have hcomp : MDifferentiableAt 𝓘(ℝ, E) I f 0 := by
    apply hexp.comp_of_eq 0 hs.mdifferentiableAt hS0
  have hl : MDifferentiableAt I I L (exp v) :=
    (contMDiff_mul_left : ContMDiff I I ∞ (fun x : G => (exp v)⁻¹ * x)).mdifferentiableAt (by norm_num)
  have hf0 : f 0 = exp v := congrArg exp hS0
  have hf : L ∘ f =
      (fun w : E => nativeLieRelativeCurve (I := I) (G := G) v (1, w)) := by
    funext w
    exact (nativeLieRelativeCurve_time_one v w).symm
  apply ContinuousLinearMap.ext
  intro w
  let DF : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I f 0
  let DE : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I exp v
  let DL : E →L[ℝ] E := mfderiv I I L (exp v)
  have he := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := I)
    (0 : E) hexp hs.mdifferentiableAt hS0 w
  have h := mfderiv_comp_apply_of_eq (I := 𝓘(ℝ, E)) (I' := I) (I'' := I)
    (0 : E) hl hcomp hf0 w
  rw [hf] at h
  change nativeLieCurveParameterJacobian (I := I) (G := G) v 1 w =
    DL (DF w) at h
  change DF w = DE
    ((mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) S 0 : E →L[ℝ] E) w) at he
  rw [hS] at he
  change DF w = DE w at he
  rw [he] at h
  exact h.symm

omit [CompleteSpace E] [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLeftTranslation_comp_inv (g : G) :
    (mfderiv I I (fun x : G => g * x) (1 : G) : E →L[ℝ] E).comp
      (mfderiv I I (fun x : G => g⁻¹ * x) g) = ContinuousLinearMap.id ℝ E := by
  have hl : MDifferentiableAt I I (fun x : G => g * x) (1 : G) :=
    (contMDiff_mul_left : ContMDiff I I ∞ (fun x : G => g * x)).mdifferentiableAt (by norm_num)
  have hr : MDifferentiableAt I I (fun x : G => g⁻¹ * x) g :=
    (contMDiff_mul_left : ContMDiff I I ∞ (fun x : G => g⁻¹ * x)).mdifferentiableAt (by norm_num)
  have he : (fun x : G => g * x) ∘ (fun x : G => g⁻¹ * x) = id := by
    funext x
    simp only [comp_apply, mul_inv_cancel_left, id_eq]
  apply ContinuousLinearMap.ext
  intro w
  have h := mfderiv_comp_apply_of_eq (I := I) (I' := I) (I'' := I) g hl hr
    (by simp only [inv_mul_cancel] : g⁻¹ * g = 1) w
  rw [he, mfderiv_id] at h
  exact h.symm

 theorem nativeLieExponential_mfderiv_eq_leftTranslation_dexp (v : E) :
    let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
      (fun z : E => nativeLieExponential (I := I) (G := G) z) v
    let L : E →L[ℝ] E := mfderiv I I
      (fun x : G => nativeLieExponential (I := I) (G := G) v * x) (1 : G)
    D = L.comp (nativeLieDexp (I := I) (G := G) v) := by
  let D : E →L[ℝ] E := mfderiv 𝓘(ℝ, E) I
    (fun z : E => nativeLieExponential (I := I) (G := G) z) v
  let L : E →L[ℝ] E := mfderiv I I
    (fun x : G => nativeLieExponential (I := I) (G := G) v * x) (1 : G)
  let R : E →L[ℝ] E := mfderiv I I
    (fun x : G => (nativeLieExponential (I := I) (G := G) v)⁻¹ * x)
      (nativeLieExponential (I := I) (G := G) v)
  change D = L.comp (nativeLieDexp (I := I) (G := G) v)
  have hi : L.comp R = ContinuousLinearMap.id ℝ E :=
    nativeLieLeftTranslation_comp_inv (I := I) (nativeLieExponential (I := I) (G := G) v)
  have hd : nativeLieDexp (I := I) (G := G) v = R.comp D := rfl
  rw [hd, ← ContinuousLinearMap.comp_assoc, hi, ContinuousLinearMap.id_comp]

 theorem nativeLieExponential_mfderiv_apply (v w : E) :
    mfderiv 𝓘(ℝ, E) I (fun z : E => nativeLieExponential (I := I) (G := G) z) v w =
      mulInvariantVectorField (I := I) (nativeLieDexp (I := I) (G := G) v w)
        (nativeLieExponential (I := I) (G := G) v) := by
  have h := congrArg (fun L : E →L[ℝ] E => L w)
    (nativeLieExponential_mfderiv_eq_leftTranslation_dexp (I := I) (G := G) v)
  exact h

end Hindman168
