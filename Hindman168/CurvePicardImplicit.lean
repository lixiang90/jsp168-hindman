import Hindman168.CurvePicardDerivative
import Mathlib.Analysis.Calculus.ImplicitFunction.ProdDomain

/-! A genuinely constructed implicit solution of the actual Picard
integral equation near a constant equilibrium with square-zero field
linearization. The state derivative is inverted explicitly; no flow or
parameter derivative is assumed. -/

namespace Hindman168
open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 noncomputable def squareZeroSubEquiv (T : E →L[ℝ] E) (hT : T.comp T = 0) : E ≃L[ℝ] E where
  toFun x := x - T x
  invFun x := x + T x
  left_inv x := by
    have h : T (T x) = 0 := congrArg (fun D : E →L[ℝ] E => D x) hT
    simp only [map_sub, h]
    abel
  right_inv x := by
    have h : T (T x) = 0 := congrArg (fun D : E →L[ℝ] E => D x) hT
    simp only [map_add, h]
    abel
  map_add' x y := by simp only [map_add]; abel
  map_smul' c x := by simp only [map_smul, smul_sub, RingHom.id_apply]
  continuous_toFun := continuous_id.sub T.continuous
  continuous_invFun := continuous_id.add T.continuous

 omit [CompleteSpace E] in
 theorem squareZeroSubEquiv_coe (T : E →L[ℝ] E) (hT : T.comp T = 0) :
    (squareZeroSubEquiv T hT : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E - T := by
  ext x
  rfl

 omit [CompleteSpace E] in
 theorem squareZeroSub_inverse (T : E →L[ℝ] E) (hT : T.comp T = 0) :
    (ContinuousLinearMap.id ℝ E - T).inverse = ContinuousLinearMap.id ℝ E + T := by
  rw [← squareZeroSubEquiv_coe T hT, ContinuousLinearMap.inverse_equiv]
  ext x
  rfl

variable {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 noncomputable def curvePicardResidual (f : E → E) (p : E × C(Icc a b, E)) : C(Icc a b, E) :=
  p.2 - curvePicard hab t₀ f p

 noncomputable def curvePicardResidualLinearization (L : E →L[ℝ] E) :
    (E × C(Icc a b, E)) →L[ℝ] C(Icc a b, E) :=
  ContinuousLinearMap.snd ℝ E C(Icc a b, E) - curvePicardLinearization hab t₀ L

 theorem curvePicardResidual_hasStrictFDerivAt_const {f : E → E} {L : E →L[ℝ] E}
    {x : E} (hf : HasStrictFDerivAt f L x) :
    HasStrictFDerivAt (curvePicardResidual hab t₀ f)
      (curvePicardResidualLinearization hab t₀ L)
      (x, ContinuousMap.const (Icc a b) x) :=
  (ContinuousLinearMap.snd ℝ E C(Icc a b, E)).hasStrictFDerivAt.sub
    (curvePicard_hasStrictFDerivAt_const hab t₀ hf)

 theorem curvePicardResidual_state_derivative (L : E →L[ℝ] E) :
    (curvePicardResidualLinearization hab t₀ L).comp
      (ContinuousLinearMap.inr ℝ E C(Icc a b, E)) =
    ContinuousLinearMap.id ℝ C(Icc a b, E) - curveVolterraLinearization hab t₀ L := by
  ext α t
  simp [curvePicardResidualLinearization, curvePicardLinearization, curveVolterraLinearization]

 theorem curvePicardResidual_state_isInvertible (L : E →L[ℝ] E) (hL : L.comp L = 0) :
    ((curvePicardResidualLinearization hab t₀ L).comp
      (ContinuousLinearMap.inr ℝ E C(Icc a b, E))).IsInvertible := by
  rw [curvePicardResidual_state_derivative]
  exact ⟨squareZeroSubEquiv _ (curveVolterraLinearization_square_zero hab t₀ L hL),
    squareZeroSubEquiv_coe _ _⟩

 theorem curvePicardResidual_state_inverse (L : E →L[ℝ] E) (hL : L.comp L = 0) :
    ((curvePicardResidualLinearization hab t₀ L).comp
      (ContinuousLinearMap.inr ℝ E C(Icc a b, E))).inverse =
    ContinuousLinearMap.id ℝ C(Icc a b, E) + curveVolterraLinearization hab t₀ L := by
  rw [curvePicardResidual_state_derivative]
  exact squareZeroSub_inverse _ (curveVolterraLinearization_square_zero hab t₀ L hL)

 noncomputable def curvePicardImplicit {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) : E → C(Icc a b, E) :=
  (curvePicardResidual_hasStrictFDerivAt_const hab t₀ hf).implicitFunctionOfProdDomain
    (curvePicardResidual_state_isInvertible hab t₀ L hL)

 theorem curvePicardImplicit_self {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) :
    curvePicardImplicit hab t₀ hf hL x = ContinuousMap.const (Icc a b) x := by
  exact ((curvePicardResidual_hasStrictFDerivAt_const hab t₀ hf).eventually_apply_eq_iff_implicitFunctionOfProdDomain
      (curvePicardResidual_state_isInvertible hab t₀ L hL)).self_of_nhds.mp rfl

 theorem curvePicardImplicit_eventually_fixed {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) (hx : f x = 0) :
    ∀ᶠ y in 𝓝 x, curvePicardImplicit hab t₀ hf hL y =
      curvePicard hab t₀ f (y, curvePicardImplicit hab t₀ hf hL y) := by
  have he := (curvePicardResidual_hasStrictFDerivAt_const hab t₀ hf).eventually_apply_implicitFunctionOfProdDomain
      (curvePicardResidual_state_isInvertible hab t₀ L hL)
  have hzero : curvePicardResidual hab t₀ f (x, ContinuousMap.const (Icc a b) x) = 0 := by
    rw [curvePicardResidual, curvePicard_const_equilibrium hab t₀ f x hx, sub_self]
  filter_upwards [he] with y hy
  exact sub_eq_zero.mp (hy.trans hzero)

 theorem curvePicardImplicit_hasStrictFDerivAt {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) :
    HasStrictFDerivAt (curvePicardImplicit hab t₀ hf hL)
      ((ContinuousLinearMap.id ℝ C(Icc a b, E) + curveVolterraLinearization hab t₀ L).comp
        (ContinuousLinearMap.const ℝ (Icc a b))) x := by
  have hd := (curvePicardResidual_hasStrictFDerivAt_const hab t₀ hf).hasStrictFDerivAt_implicitFunctionOfProdDomain
      (curvePicardResidual_state_isInvertible hab t₀ L hL)
  rw [curvePicardResidual_state_inverse hab t₀ L hL] at hd
  convert! hd using 1
  ext y t
  simp [curvePicardResidualLinearization, curvePicardLinearization,
    curveVolterraLinearization]

end Hindman168
