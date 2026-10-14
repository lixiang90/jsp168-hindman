import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc

/-! The actual primitive integral as a bounded linear operator on the
Banach space of continuous curves on a closed interval. Its pointwise
formula, norm bound and compatibility with actual linear maps are proved. -/

namespace Hindman168
open Set MeasureTheory intervalIntegral Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {a b : ℝ} (hab : a ≤ b) (t₀ : Icc a b)

 noncomputable def curveClippedExtension (α : C(Icc a b, E)) : ℝ → E :=
  fun t => α (projIcc a b hab t)

 omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem curveClippedExtension_continuous (α : C(Icc a b, E)) :
    Continuous (curveClippedExtension hab α) := α.continuous.comp continuous_projIcc

 omit [NormedSpace ℝ E] [CompleteSpace E] in
 theorem curveClippedExtension_of_mem (α : C(Icc a b, E)) (t : Icc a b) :
    curveClippedExtension hab α t = α t := by
  simp only [curveClippedExtension, projIcc_of_mem hab t.2]

 noncomputable def curvePrimitive (α : C(Icc a b, E)) : C(Icc a b, E) where
  toFun t := ∫ s in (t₀ : ℝ)..(t : ℝ), curveClippedExtension hab α s
  continuous_toFun :=
    (differentiable_integral_of_continuous (curveClippedExtension_continuous hab α)).continuous.comp
      continuous_subtype_val

 theorem curvePrimitive_apply (α : C(Icc a b, E)) (t : Icc a b) :
    curvePrimitive hab t₀ α t = ∫ s in (t₀ : ℝ)..(t : ℝ),
      curveClippedExtension hab α s := rfl

 theorem curvePrimitive_norm_le (α : C(Icc a b, E)) :
    ‖curvePrimitive hab t₀ α‖ ≤ (b - a) * ‖α‖ := by
  apply (ContinuousMap.norm_le _ (mul_nonneg (sub_nonneg.mpr hab) (norm_nonneg α))).mpr
  intro t
  have hi : ‖curvePrimitive hab t₀ α t‖ ≤ ‖α‖ * |(t : ℝ) - t₀| := by
    exact intervalIntegral.norm_integral_le_of_norm_le_const
      (fun s _ => α.norm_coe_le_norm (projIcc a b hab s))
  have ht : |(t : ℝ) - t₀| ≤ b - a := by
    rw [abs_le]
    constructor <;> linarith [t.2.1, t.2.2, t₀.2.1, t₀.2.2]
  exact hi.trans (by nlinarith [norm_nonneg α])

 noncomputable def curveVolterra : C(Icc a b, E) →L[ℝ] C(Icc a b, E) :=
  LinearMap.mkContinuous
    { toFun := curvePrimitive hab t₀
      map_add' := by
        intro α β
        ext t
        exact intervalIntegral.integral_add
          ((curveClippedExtension_continuous hab α).intervalIntegrable t₀ t)
          ((curveClippedExtension_continuous hab β).intervalIntegrable t₀ t)
      map_smul' := by
        intro c α
        ext t
        exact intervalIntegral.integral_smul c (curveClippedExtension hab α) }
    (b - a) (curvePrimitive_norm_le hab t₀)

 theorem curveVolterra_apply (α : C(Icc a b, E)) (t : Icc a b) :
    curveVolterra hab t₀ α t = ∫ s in (t₀ : ℝ)..(t : ℝ),
      curveClippedExtension hab α s := rfl

 theorem curveVolterra_norm_le : ‖curveVolterra (E := E) hab t₀‖ ≤ b - a := by
  exact LinearMap.mkContinuous_norm_le _ (sub_nonneg.mpr hab) _

 theorem curveVolterra_commutes_clm (L : E →L[ℝ] F) (α : C(Icc a b, E)) :
    curveVolterra hab t₀ (ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L α) =
      ContinuousLinearMap.compLeftContinuous ℝ (Icc a b) L (curveVolterra hab t₀ α) := by
  ext t
  exact L.intervalIntegral_comp_comm
    ((curveClippedExtension_continuous hab α).intervalIntegrable t₀ t)

end Hindman168
