import Hindman168.CurveSuperpositionDerivative
import Hindman168.CurveVolterraOperator
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Add

/-! The genuine Picard curve operator and its strict linearization at
an equilibrium constant curve. Its derivative is computed from actual
superposition and the actual bounded primitive integral operator. -/

namespace Hindman168
open Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 noncomputable def curvePicard (f : E → E) (p : E × C(Icc a b, E)) : C(Icc a b, E) :=
  ContinuousMap.const (Icc a b) p.1 + curveVolterra hab t₀ (curveSuperposition f p.2)

 theorem curvePicard_apply_of_continuous (f : E → E) (x : E) (α : C(Icc a b, E))
    (hc : Continuous (fun t => f (α t))) (t : Icc a b) :
    curvePicard hab t₀ f (x, α) t =
      x + ∫ s in (t₀ : ℝ)..(t : ℝ), f (curveClippedExtension hab α s) := by
  change x + (curveVolterra hab t₀ (curveSuperposition f α)) t = _
  rw [curveVolterra_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact curveSuperposition_apply_of_continuous f α hc (projIcc a b hab s)

 noncomputable def curvePicardLinearization (L : E →L[ℝ] E) :
    (E × C(Icc a b, E)) →L[ℝ] C(Icc a b, E) :=
  (ContinuousLinearMap.const ℝ (Icc a b)).comp (ContinuousLinearMap.fst ℝ E C(Icc a b, E)) +
    (curveVolterra hab t₀).comp
      ((ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L).comp
        (ContinuousLinearMap.snd ℝ E C(Icc a b, E)))

 theorem curvePicard_hasStrictFDerivAt_const {f : E → E} {L : E →L[ℝ] E}
    {x : E} (hf : HasStrictFDerivAt f L x) :
    HasStrictFDerivAt (curvePicard hab t₀ f) (curvePicardLinearization hab t₀ L)
      (x, ContinuousMap.const (Icc a b) x) := by
  have h₁ := (ContinuousLinearMap.const ℝ (Icc a b) : E →L[ℝ] C(Icc a b, E)).hasStrictFDerivAt.comp
    (x, ContinuousMap.const (Icc a b) x)
    (ContinuousLinearMap.fst ℝ E C(Icc a b, E)).hasStrictFDerivAt
  have h₂ := (curveSuperposition_hasStrictFDerivAt_const (K := Icc a b) hf).comp
    (x, ContinuousMap.const (Icc a b) x)
    (ContinuousLinearMap.snd ℝ E C(Icc a b, E)).hasStrictFDerivAt
  exact h₁.add ((curveVolterra hab t₀).hasStrictFDerivAt.comp
    (x, ContinuousMap.const (Icc a b) x) h₂)

 theorem curvePicard_const_equilibrium (f : E → E) (x : E) (hx : f x = 0) :
    curvePicard hab t₀ f (x, ContinuousMap.const (Icc a b) x) =
      ContinuousMap.const (Icc a b) x := by
  rw [curvePicard, curveSuperposition_const, hx]
  simp

 noncomputable def curveVolterraLinearization (L : E →L[ℝ] E) :
    C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  (curveVolterra hab t₀).comp (ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L)

 theorem curvePicard_state_derivative (L : E →L[ℝ] E) :
    (curvePicardLinearization hab t₀ L).comp
      (ContinuousLinearMap.inr ℝ E C(Icc a b, E)) = curveVolterraLinearization hab t₀ L := by
  ext α t
  simp [curvePicardLinearization, curveVolterraLinearization]

 theorem curveVolterraLinearization_square_zero (L : E →L[ℝ] E)
    (hL : L.comp L = 0) :
    (curveVolterraLinearization hab t₀ L).comp
      (curveVolterraLinearization hab t₀ L) = 0 := by
  ext α t
  change (curveVolterra hab t₀
    (ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L
      (curveVolterra hab t₀
        (ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L α)))) t = 0
  rw [← curveVolterra_commutes_clm hab t₀]
  have hz : ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L
      (ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L α) = 0 := by
    ext s
    exact congrArg (fun D : E →L[ℝ] E => D (α s)) hL
  rw [hz, map_zero, map_zero]
  rfl

end Hindman168
