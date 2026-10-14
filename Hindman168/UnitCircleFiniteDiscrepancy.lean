import Hindman168.UnitCircleUniformFourierApproximation
import Hindman168.FiniteComplexSetMean

namespace Hindman168
open MeasureTheory
open scoped BigOperators Classical Topology

/-- The ACTUAL finite orbit mean minus normalized Haar integral. -/
noncomputable def unitCircleFiniteDiscrepancy {α : Type*} (s : Finset α)
    (f : α → UnitAddCircle) : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ where
  toFun F := finiteComplexSetMean s (fun a => F (f a))-∫ t, F t ∂AddCircle.haarAddCircle
  map_add' F G := by
    have hF := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
      (μ := AddCircle.haarAddCircle)
    have hG := G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
      (μ := AddCircle.haarAddCircle)
    simp only [ContinuousMap.add_apply, finiteComplexSetMean, Finset.sum_add_distrib,
      add_div, integral_add hF hG]
    ring
  map_smul' c F := by
    simp only [ContinuousMap.smul_apply, finiteComplexSetMean, ← Finset.smul_sum,
      smul_div_assoc, integral_smul, smul_sub, RingHom.id_apply]

theorem unit_circle_finite_discrepancy_norm_bound {α : Type*} (s : Finset α)
    (f : α → UnitAddCircle) (F : C(UnitAddCircle, ℂ)) :
    ‖unitCircleFiniteDiscrepancy s f F‖ ≤ 2*‖F‖ := by
  have hm := finiteComplexSetMean_norm_bound s (fun a => F (f a)) ‖F‖ (norm_nonneg F)
    (fun a _ => F.norm_coe_le_norm _)
  have hi : ‖∫ t, F t ∂AddCircle.haarAddCircle‖ ≤ ‖F‖ := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := AddCircle.haarAddCircle)
        (Filter.Eventually.of_forall (fun t => F.norm_coe_le_norm t))
  exact (norm_sub_le _ _).trans (by linarith only [hm, hi])

theorem unit_circle_finite_nonzero_fourier_discrepancy {α : Type*} (s : Finset α)
    (f : α → UnitAddCircle) (k : ℤ) (hk : k ≠ 0) :
    unitCircleFiniteDiscrepancy s f (fourier k) =
      finiteComplexSetMean s (fun a => fourier k (f a)) := by
  change _-∫ t, fourier k t ∂AddCircle.haarAddCircle = _
  rw [unit_circle_fourier_haar_integral, if_neg hk, sub_zero]

theorem unit_circle_finite_zero_fourier_discrepancy {α : Type*} (s : Finset α)
    (hs : s.Nonempty) (f : α → UnitAddCircle) :
    unitCircleFiniteDiscrepancy s f (fourier 0) = 0 := by
  change finiteComplexSetMean s (fun a => fourier 0 (f a))-
    ∫ t, fourier 0 t ∂AddCircle.haarAddCircle = 0
  rw [unit_circle_fourier_haar_integral, if_pos rfl]
  simp only [fourier_zero, finiteComplexSetMean, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [div_self (by exact_mod_cast hs.card_pos.ne'), sub_self]

theorem unit_circle_finite_fourier_large_frequency {α : Type*} (s : Finset α)
    (hs : s.Nonempty) (f : α → UnitAddCircle) (c : ℤ →₀ ℂ) (B δ : ℝ)
    (hB : 0 < B) (hδ : 0 < δ) (hbudget : ∑ k ∈ c.support, ‖c k‖ ≤ B)
    (hlarge : δ/2 ≤ ‖unitCircleFiniteDiscrepancy s f
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ))))‖) :
    ∃ k ∈ c.support, k ≠ 0 ∧ δ/(4*B) ≤ ‖unitCircleFiniteDiscrepancy s f (fourier k)‖ := by
  by_contra! h
  have hmode : ∀ k ∈ c.support, ‖unitCircleFiniteDiscrepancy s f (fourier k)‖ ≤ δ/(4*B) := by
    intro k hk
    by_cases hz : k=0
    · rw [hz, unit_circle_finite_zero_fourier_discrepancy s hs f, norm_zero]
      positivity
    · exact (h k hk hz).le
  have heq : unitCircleFiniteDiscrepancy s f
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ)))) =
      ∑ k ∈ c.support, c k*unitCircleFiniteDiscrepancy s f (fourier k) := by
    rw [Finsupp.sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hb : ‖unitCircleFiniteDiscrepancy s f
      (c.sum (fun k a => a • (fourier k : C(UnitAddCircle, ℂ))))‖ ≤ δ/4 := by
    rw [heq]
    calc
      _ ≤ ∑ k ∈ c.support, ‖c k*unitCircleFiniteDiscrepancy s f (fourier k)‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ c.support, ‖c k‖*(δ/(4*B)) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hmode k hk) (norm_nonneg _)
      _ = (∑ k ∈ c.support, ‖c k‖)*(δ/(4*B)) := by rw [Finset.sum_mul]
      _ ≤ B*(δ/(4*B)) := mul_le_mul_of_nonneg_right hbudget (by positivity)
      _ = δ/4 := by field_simp
  linarith only [hδ, hlarge, hb]

end Hindman168
