import Hindman168.UnitTorusSetDistanceBump

/-! Dense actual hits and a PROVED small actual neighborhood measure imply
TRUE product-Haar discrepancy in one actual UNIT Lipschitz observable. -/
namespace Hindman168
open Set MeasureTheory
open scoped BigOperators Classical

theorem unit_torus_set_distance_bump_dense_mean {ι α : Type*} [Fintype ι]
    (s : Finset α) (hs : s.Nonempty) (f : α → UnitAddTorus ι)
    (S : Set (UnitAddTorus ι)) (r δ : ℝ) (hr : 0 ≤ r)
    (hdense : δ*(s.card : ℝ) ≤ (s.filter (fun a => f a ∈ S)).card) :
    δ*r ≤ (∑ a ∈ s, unitTorusSetDistanceBump r S (f a))/(s.card : ℝ) := by
  have hc : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have ht : ((s.filter (fun a => f a ∈ S)).card : ℝ)*r ≤ ∑ a ∈ s, unitTorusSetDistanceBump r S (f a) := by
    calc
      _ = ∑ _a ∈ s.filter (fun a => f a ∈ S), r := by simp only [Finset.sum_const,nsmul_eq_mul]
      _ = ∑ a ∈ s.filter (fun a => f a ∈ S), unitTorusSetDistanceBump r S (f a) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact (unit_torus_set_distance_bump_mem r hr S (Finset.mem_filter.mp ha).2).symm
      _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun a _ _ => unit_torus_set_distance_bump_nonneg r S (f a))
  apply (le_div_iff₀ hc).mpr
  have hm := mul_le_mul_of_nonneg_right hdense hr
  nlinarith

theorem unit_torus_set_distance_discrepancy {ι α : Type*} [Fintype ι]
    (s : Finset α) (hs : s.Nonempty) (f : α → UnitAddTorus ι)
    (S : Set (UnitAddTorus ι)) (hS : S.Nonempty) (r δ : ℝ) (hr : 0 ≤ r) (hδ : 0 ≤ δ)
    (hdense : δ*(s.card : ℝ) ≤ (s.filter (fun a => f a ∈ S)).card)
    (hmeasure : (Measure.pi (fun _ : ι => AddCircle.haarAddCircle))
      (Metric.thickening r S) ≤ ENNReal.ofReal (δ/2)) :
    δ*r/2 ≤ ‖unitTorusFiniteDiscrepancy s f (unitTorusSetDistanceObservable r S)‖ := by
  have hm := unit_torus_set_distance_bump_dense_mean s hs f S r δ hr hdense
  have hi := unit_torus_set_distance_bump_haar_bound r hr S hS
  have hvolume := ENNReal.toReal_le_of_le_ofReal (by positivity : 0 ≤ δ/2) hmeasure
  have hi' : (∫ x, unitTorusSetDistanceBump r S x ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) ≤ r*(δ/2) :=
    hi.trans (mul_le_mul_of_nonneg_left hvolume hr)
  have he : finiteComplexSetMean s (fun a => unitTorusSetDistanceObservable r S (f a)) =
      (((∑ a ∈ s, unitTorusSetDistanceBump r S (f a))/(s.card : ℝ) : ℝ) : ℂ) := by
    simp only [finiteComplexSetMean,unitTorusSetDistanceObservable,ContinuousMap.coe_mk,
      Complex.ofReal_div,Complex.ofReal_sum,Complex.ofReal_natCast]
  change δ*r/2 ≤ ‖finiteComplexSetMean s (fun a => unitTorusSetDistanceObservable r S (f a))-
    ∫ x, unitTorusSetDistanceObservable r S x ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle)‖
  rw [he]
  change δ*r/2 ≤ ‖((_ : ℝ) : ℂ)-∫ x, (unitTorusSetDistanceBump r S x : ℂ)
    ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle)‖
  have hreal : (∫ x, (unitTorusSetDistanceBump r S x : ℂ)
      ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle)) =
      ((∫ x, unitTorusSetDistanceBump r S x ∂Measure.pi (fun _ : ι => AddCircle.haarAddCircle) : ℝ) : ℂ) :=
    integral_ofReal
  rw [hreal,← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
  exact (show δ*r/2 ≤ _ from by linarith [hm,hi']).trans (le_abs_self _)

end Hindman168
