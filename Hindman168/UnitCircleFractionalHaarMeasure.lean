import Hindman168.UnitCircleFractionalRepresentative
import Hindman168.RealAffineIntegerSlabMeasure

/-! ACTUAL [0,1) fractional-coordinate measure transport under canonical
circle Haar. The interval convention is retained exactly, not changed on samples. -/
namespace Hindman168
open Set MeasureTheory

theorem unit_circle_measure_preserving_ico :
    MeasurePreserving (fun x : ℝ => (x : UnitAddCircle))
      (volume.restrict (Ico (0 : ℝ) 1)) AddCircle.haarAddCircle := by
  have hv : (volume : Measure UnitAddCircle)=AddCircle.haarAddCircle := by
    simpa using (AddCircle.volume_eq_smul_haarAddCircle (T := (1 : ℝ)))
  have hm := AddCircle.measurePreserving_mk (1 : ℝ) 0
  simpa only [zero_add,hv,MeasureTheory.restrict_Ico_eq_restrict_Ioc] using hm

theorem unit_circle_fractional_haar_preimage (S : Set ℝ) (hS : MeasurableSet S) :
    AddCircle.haarAddCircle (unitCircleFractionalRepresentative ⁻¹' S)=
      volume (S ∩ Ico (0 : ℝ) 1) := by
  have hm := unit_circle_measure_preserving_ico.measure_preimage
    (unit_circle_fractional_representative_measurable hS).nullMeasurableSet
  rw [Measure.restrict_apply (AddCircle.measurable_mk' (a := (1 : ℝ))
    (unit_circle_fractional_representative_measurable hS))] at hm
  have he : (fun x : ℝ => (x : UnitAddCircle)) ⁻¹'
      (unitCircleFractionalRepresentative ⁻¹' S) ∩ Ico (0 : ℝ) 1 = S ∩ Ico (0 : ℝ) 1 := by
    ext x
    constructor
    · rintro ⟨hx,hm⟩
      change unitCircleFractionalRepresentative (x : UnitAddCircle) ∈ S at hx
      rw [unit_circle_fractional_representative_real,
        Int.fract_eq_self.mpr hm] at hx
      exact ⟨hx,hm⟩
    · rintro ⟨hx,hm⟩
      refine ⟨?_,hm⟩
      change unitCircleFractionalRepresentative (x : UnitAddCircle) ∈ S
      rw [unit_circle_fractional_representative_real,Int.fract_eq_self.mpr hm]
      exact hx
  rw [he] at hm
  exact hm.symm

theorem bounded_unit_circle_fractional_slab_measure (T Z : ℝ) :
    ∃ K : ℕ, ∀ (θ z ε : ℝ), |θ| ≤ T → |z| ≤ Z → ε ≤ 1 → z ≠ 0 →
      AddCircle.haarAddCircle {x : UnitAddCircle |
        ‖((θ+z*unitCircleFractionalRepresentative x : ℝ) : UnitAddCircle)‖ ≤ ε} ≤
          ENNReal.ofReal (((Finset.Icc (-(K : ℤ)) (K : ℤ)).card : ℝ)*(2*ε/|z|)) := by
  obtain ⟨K,hcover⟩ := bounded_real_circle_slab_integer_cover T Z
  refine ⟨K,?_⟩
  intro θ z ε hθ hz hε hz0
  let S : Set ℝ := {x | ‖((θ+z*x : ℝ) : UnitAddCircle)‖ ≤ ε}
  have hf : Measurable (fun x : ℝ => ((θ+z*x : ℝ) : UnitAddCircle)) :=
    AddCircle.measurable_mk'.comp (measurable_const.add (measurable_const.mul measurable_id))
  have hS : MeasurableSet S := hf.norm measurableSet_Iic
  change AddCircle.haarAddCircle (unitCircleFractionalRepresentative ⁻¹' S) ≤ _
  rw [unit_circle_fractional_haar_preimage S hS]
  rcases lt_or_gt_of_ne hz0 with hneg | hpos
  · have he : S={x | ‖(((-θ)+(-z)*x : ℝ) : UnitAddCircle)‖ ≤ ε} := by
      ext x
      simp only [S,mem_setOf_eq,show -θ+(-z)*x=-(θ+z*x) by ring,AddCircle.coe_neg,norm_neg]
    rw [he,abs_of_neg hneg]
    apply real_affine_integer_slab_measure _ (-θ) (-z) ε (neg_pos.mpr hneg)
      (Finset.Icc (-(K : ℤ)) (K : ℤ))
    intro x hx
    exact hcover (-θ) (-z) ε x (by simpa only [abs_neg] using hθ)
      (by simpa only [abs_neg] using hz) hε ⟨hx.2.1,hx.2.2.le⟩ hx.1
  · rw [abs_of_pos hpos]
    apply real_affine_integer_slab_measure _ θ z ε hpos (Finset.Icc (-(K : ℤ)) (K : ℤ))
    intro x hx
    exact hcover θ z ε x hθ hz hε ⟨hx.2.1,hx.2.2.le⟩ hx.1

end Hindman168
