import Hindman168.CurveSuperpositionSmooth
import Hindman168.CurvePicardImplicit
import Mathlib.Analysis.Calculus.ImplicitContDiff

/-! Smoothness of the retained actual Picard construction. The field's
genuine smoothness is lifted by the proved superposition theorem;
the primitive is the original bounded integral operator. The existing
implicit curve, rather than a supplied replacement flow, is proved smooth. -/

namespace Hindman168
open Set Topology
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 theorem curvePicard_contDiffAt_smooth {f : E → E} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (curvePicard hab t₀ f) (x, ContinuousMap.const (Icc a b) x) := by
  have h₁ := (ContinuousLinearMap.const ℝ (Icc a b) : E →L[ℝ] C(Icc a b, E)).contDiff (n := ∞) |>.contDiffAt.comp
    (x, ContinuousMap.const (Icc a b) x) contDiffAt_fst
  have h₂ := (curveSuperposition_contDiffAt_smooth (K := Icc a b) hf).comp
    (x, ContinuousMap.const (Icc a b) x) contDiffAt_snd
  exact h₁.add ((curveVolterra (E := E) hab t₀).contDiff.contDiffAt.comp
    (x, ContinuousMap.const (Icc a b) x) h₂)

 theorem curvePicardResidual_contDiffAt_smooth {f : E → E} {x : E}
    (hf : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (curvePicardResidual hab t₀ f) (x, ContinuousMap.const (Icc a b) x) :=
  contDiffAt_snd.sub (curvePicard_contDiffAt_smooth hab t₀ hf)

 theorem curvePicardImplicit_contDiffAt_smooth {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) (hs : ContDiffAt ℝ ∞ f x) :
    ContDiffAt ℝ ∞ (curvePicardImplicit hab t₀ hf hL) x := by
  let φ := (curvePicardResidual_hasStrictFDerivAt_const hab t₀ hf).implicitFunctionDataOfProdDomain
    (curvePicardResidual_state_isInvertible hab t₀ L hL)
  have hφ := φ.contDiffAt_implicitFunction
    (curvePicardResidual_contDiffAt_smooth hab t₀ hs) contDiffAt_fst (by norm_num : (∞ : ℕ∞ω) ≠ 0)
  have he : ContDiffAt ℝ ∞
      (fun y : E => (curvePicardResidual hab t₀ f (x, ContinuousMap.const (Icc a b) x), y)) x :=
    contDiffAt_const.prodMk contDiffAt_id
  exact (hφ.comp x he).snd

 theorem curvePicardImplicit_endpoint_contDiffAt_smooth {f : E → E} {L : E →L[ℝ] E} {x : E}
    (hf : HasStrictFDerivAt f L x) (hL : L.comp L = 0) (hs : ContDiffAt ℝ ∞ f x)
    (t : Icc a b) :
    ContDiffAt ℝ ∞ (fun y => curvePicardImplicit hab t₀ hf hL y t) x :=
  (ContinuousMap.evalCLM ℝ t : C(Icc a b, E) →L[ℝ] E).contDiff.contDiffAt.comp x
    (curvePicardImplicit_contDiffAt_smooth hab t₀ hf hL hs)

end Hindman168
