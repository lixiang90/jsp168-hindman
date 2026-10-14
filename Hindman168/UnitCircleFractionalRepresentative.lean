import Hindman168.UnitCircleNormBump
import Hindman168.RoughExactInterpolationModOne

/-! ACTUAL measurable [0,1) circle representatives. Away from the true
coordinate boundary, close circle points have the actual small real difference. -/
namespace Hindman168
open Set MeasureTheory

noncomputable def unitCircleFractionalRepresentative (x : UnitAddCircle) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0 x).val

theorem unit_circle_fractional_representative_mem (x : UnitAddCircle) :
    unitCircleFractionalRepresentative x ∈ Ico (0 : ℝ) 1 := by
  simpa only [unitCircleFractionalRepresentative,zero_add] using (AddCircle.equivIco (1 : ℝ) 0 x).property

theorem unit_circle_fractional_representative_coe (x : UnitAddCircle) :
    (unitCircleFractionalRepresentative x : UnitAddCircle)=x := AddCircle.coe_equivIco

theorem unit_circle_fractional_representative_real (x : ℝ) :
    unitCircleFractionalRepresentative (x : UnitAddCircle)=Int.fract x := by
  simpa only [unitCircleFractionalRepresentative,div_one,mul_one] using
    (AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x)

theorem unit_circle_fractional_representative_measurable :
    Measurable unitCircleFractionalRepresentative :=
  measurable_subtype_coe.comp (AddCircle.measurableEquivIco (1 : ℝ) 0).measurable

theorem unit_circle_fractional_representative_integer_bound (x : UnitAddCircle) (k : ℤ) :
    ‖x‖ ≤ |unitCircleFractionalRepresentative x-(k : ℝ)| := by
  calc
    ‖x‖=‖(unitCircleFractionalRepresentative x : UnitAddCircle)‖ :=
      congrArg norm (unit_circle_fractional_representative_coe x).symm
    _ ≤ _ := (rough_mod_one_near_integer_iff _ _).mpr ⟨k,le_rfl⟩

theorem unit_circle_fractional_representative_difference {x y : UnitAddCircle} {r : ℝ}
    (hx : r < ‖x‖) (hxy : dist x y < r) :
    |unitCircleFractionalRepresentative x-unitCircleFractionalRepresentative y|=dist x y := by
  let d := unitCircleFractionalRepresentative x-unitCircleFractionalRepresentative y
  let k := round d
  have he : (d : UnitAddCircle)=x-y := by
    rw [show d=_ from rfl,AddCircle.coe_sub,unit_circle_fractional_representative_coe,
      unit_circle_fractional_representative_coe]
  have hd : |d-(k : ℝ)|=dist x y := by
    rw [show k=round d from rfl,← UnitAddCircle.norm_eq,he,dist_eq_norm]
  obtain ⟨hl,hu⟩ := abs_lt.mp (hd.trans_lt hxy)
  obtain ⟨hx0,hx1⟩ := unit_circle_fractional_representative_mem x
  obtain ⟨hy0,hy1⟩ := unit_circle_fractional_representative_mem y
  dsimp only [d] at hl hu
  have hk : k=0 := by
    by_contra hk0
    rcases lt_or_gt_of_ne hk0 with hkneg | hkpos
    · have hkr : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
      have hn := unit_circle_fractional_representative_integer_bound x 0
      rw [Int.cast_zero,sub_zero,abs_of_nonneg hx0] at hn
      linarith
    · have hkr : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
      have hn := unit_circle_fractional_representative_integer_bound x 1
      rw [Int.cast_one,abs_of_neg (by linarith : unitCircleFractionalRepresentative x-1 < 0)] at hn
      linarith
  simpa only [hk,Int.cast_zero,sub_zero] using hd

end Hindman168
