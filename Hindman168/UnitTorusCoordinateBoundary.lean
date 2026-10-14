import Hindman168.UnitCircleFractionalRepresentative
import Hindman168.UnitTorusFiniteDiscrepancy

/-! ACTUAL coordinate-boundary strips under SAME product-circle Haar.
Their union measure and fractional-coordinate neighborhood control are proved. -/
namespace Hindman168
open Set MeasureTheory
open scoped BigOperators Classical

noncomputable def unitTorusCoordinateBoundary {ι : Type*} [Fintype ι] (r : ℝ) :
    Set (UnitAddTorus ι) := {x | ∃ i, ‖x i‖ ≤ r}

theorem unit_torus_coordinate_boundary_measurable {ι : Type*} [Fintype ι] (r : ℝ) :
    MeasurableSet (unitTorusCoordinateBoundary (ι := ι) r) := by
  have he : unitTorusCoordinateBoundary (ι := ι) r =
      ⋃ i, (fun x : UnitAddTorus ι => x i) ⁻¹' Metric.closedBall 0 r := by
    ext x
    simp only [unitTorusCoordinateBoundary,mem_setOf_eq,mem_iUnion,mem_preimage,
      Metric.mem_closedBall,dist_zero_right]
  rw [he]
  exact MeasurableSet.iUnion (fun i => measurableSet_closedBall.preimage (measurable_pi_apply i))

theorem unit_torus_coordinate_boundary_measure {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 2*r ≤ 1) :
    (Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) (unitTorusCoordinateBoundary r) ≤
      ENNReal.ofReal ((Fintype.card ι : ℝ)*(2*r)) := by
  let μ : Measure (UnitAddTorus ι) := Measure.pi (fun _ : ι => AddCircle.haarAddCircle)
  have he : unitTorusCoordinateBoundary (ι := ι) r =
      ⋃ i ∈ (Finset.univ : Finset ι), (fun x : UnitAddTorus ι => x i) ⁻¹' Metric.closedBall 0 r := by
    ext x
    simp only [unitTorusCoordinateBoundary,mem_setOf_eq,mem_iUnion,Finset.mem_univ,true_and,
      mem_preimage,Metric.mem_closedBall,dist_zero_right,exists_prop]
  rw [he]
  apply (measure_biUnion_finset_le _ _).trans
  change (∑ i : ι, μ ((fun x : UnitAddTorus ι => x i) ⁻¹' Metric.closedBall (0 : UnitAddCircle) r)) ≤ _
  have hm (i : ι) : μ ((fun x : UnitAddTorus ι => x i) ⁻¹' Metric.closedBall 0 r)=
      ENNReal.ofReal (2*r) := by
    rw [(measurePreserving_eval (fun _ : ι => AddCircle.haarAddCircle) i).measure_preimage
      measurableSet_closedBall.nullMeasurableSet,unit_circle_haar_closed_ball r hr]
  simp_rw [hm]
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    ENNReal.ofReal_mul (Nat.cast_nonneg (Fintype.card ι)),ENNReal.ofReal_natCast]

theorem unit_torus_fractional_difference_outside_boundary {ι : Type*} [Fintype ι]
    {x y : UnitAddTorus ι} {r : ℝ} (hx : x ∉ unitTorusCoordinateBoundary r)
    (hxy : dist x y < r) :
    ∀ i, |unitCircleFractionalRepresentative (x i)-unitCircleFractionalRepresentative (y i)| ≤ dist x y := by
  intro i
  have hxi : r < ‖x i‖ := by
    by_contra! h
    exact hx ⟨i,h⟩
  have hdi : dist (x i) (y i) ≤ dist x y := dist_le_pi_dist x y i
  rw [unit_circle_fractional_representative_difference hxi (hdi.trans_lt hxy)]
  exact hdi

end Hindman168
