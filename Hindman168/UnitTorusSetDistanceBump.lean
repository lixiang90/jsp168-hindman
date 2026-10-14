import Hindman168.UnitTorusFractionalSlab

/-! Genuine UNIT Lipschitz torus cutoff from distance to an arbitrary
nonempty slab. Its radius is retained as the actual peak height. -/
namespace Hindman168
open Set MeasureTheory Metric
open scoped Topology

noncomputable def unitTorusSetDistanceBump {ι : Type*} [Fintype ι]
    (r : ℝ) (S : Set (UnitAddTorus ι)) (x : UnitAddTorus ι) : ℝ := max 0 (r-infDist x S)

theorem unit_torus_set_distance_bump_nonneg {ι : Type*} [Fintype ι]
    (r : ℝ) (S : Set (UnitAddTorus ι)) (x : UnitAddTorus ι) :
    0 ≤ unitTorusSetDistanceBump r S x := le_max_left _ _

theorem unit_torus_set_distance_bump_le {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (S : Set (UnitAddTorus ι)) (x : UnitAddTorus ι) :
    unitTorusSetDistanceBump r S x ≤ r := max_le hr (sub_le_self _ infDist_nonneg)

theorem unit_torus_set_distance_bump_mem {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (S : Set (UnitAddTorus ι)) {x : UnitAddTorus ι} (hx : x ∈ S) :
    unitTorusSetDistanceBump r S x=r := by
  rw [unitTorusSetDistanceBump,infDist_zero_of_mem hx,sub_zero,max_eq_right hr]

theorem unit_torus_set_distance_bump_lipschitz {ι : Type*} [Fintype ι]
    (r : ℝ) (S : Set (UnitAddTorus ι)) : LipschitzWith 1 (unitTorusSetDistanceBump r S) := by
  have hf : LipschitzWith 1 (fun x : UnitAddTorus ι => r-infDist x S) := by
    apply LipschitzWith.mk_one
    intro x y
    simpa only [Real.dist_eq,sub_sub_sub_cancel_left,abs_sub_comm,NNReal.coe_one,one_mul] using
      (lipschitz_infDist_pt S).dist_le_mul x y
  exact hf.const_max 0

noncomputable def unitTorusSetDistanceObservable {ι : Type*} [Fintype ι]
    (r : ℝ) (S : Set (UnitAddTorus ι)) : C(UnitAddTorus ι,ℂ) :=
  ⟨fun x => (unitTorusSetDistanceBump r S x : ℂ),
    Complex.continuous_ofReal.comp (unit_torus_set_distance_bump_lipschitz r S).continuous⟩

theorem unit_torus_set_distance_observable_unit {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (S : Set (UnitAddTorus ι)) :
    unitTorusSetDistanceObservable r S ∈ unitLipschitzObservables (UnitAddTorus ι) := by
  refine ⟨?_,?_⟩
  · apply LipschitzWith.mk_one
    intro x y
    change dist (Complex.ofReal (unitTorusSetDistanceBump r S x))
      (Complex.ofReal (unitTorusSetDistanceBump r S y)) ≤ dist x y
    rw [Complex.isometry_ofReal.dist_eq]
    simpa only [NNReal.coe_one,one_mul] using (unit_torus_set_distance_bump_lipschitz r S).dist_le_mul x y
  · intro x
    change ‖(unitTorusSetDistanceBump r S x : ℂ)‖ ≤ 1
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (unit_torus_set_distance_bump_nonneg r S x)]
    exact (unit_torus_set_distance_bump_le r hr S x).trans hr1

theorem unit_torus_set_distance_bump_haar_bound {ι : Type*} [Fintype ι]
    (r : ℝ) (hr : 0 ≤ r) (S : Set (UnitAddTorus ι)) (hS : S.Nonempty) :
    (∫ x, unitTorusSetDistanceBump r S x ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) ≤
      r*((Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) (Metric.thickening r S)).toReal := by
  let μ : Measure (UnitAddTorus ι) := Measure.pi (fun _ : ι => AddCircle.haarAddCircle)
  let A := Metric.thickening r S
  have hA : MeasurableSet A := Metric.isOpen_thickening.measurableSet
  have hf : Integrable (unitTorusSetDistanceBump r S) μ :=
    (unit_torus_set_distance_bump_lipschitz r S).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : Integrable (A.indicator (fun _ => r)) μ := (integrable_const r).indicator hA
  have hle : unitTorusSetDistanceBump r S ≤ A.indicator (fun _ => r) := by
    intro x
    by_cases hx : x ∈ A
    · rw [indicator_of_mem hx]
      exact unit_torus_set_distance_bump_le r hr S x
    · rw [indicator_of_notMem hx]
      have hd : r ≤ infDist x S := by
        exact le_of_not_gt (fun h => hx ((Metric.mem_thickening_iff_infDist_lt hS).mpr h))
      exact max_le le_rfl (sub_nonpos.mpr hd)
  have hi := integral_mono hf hg hle
  rw [integral_indicator hA,integral_const] at hi
  simpa only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm] using hi

end Hindman168
