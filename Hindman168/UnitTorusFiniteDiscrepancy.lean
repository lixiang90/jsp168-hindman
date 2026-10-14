import Hindman168.UnitTorusUniformFourierApproximation
import Hindman168.FiniteComplexSetMean

namespace Hindman168
open MeasureTheory
open scoped BigOperators Classical Topology

noncomputable def unitTorusFiniteDiscrepancy {κ α : Type*} [Fintype κ]
    (s : Finset α) (f : α → UnitAddTorus κ) : C(UnitAddTorus κ, ℂ) →ₗ[ℂ] ℂ where
  toFun F := finiteComplexSetMean s (fun a => F (f a))-
    ∫ t, F t ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)
  map_add' F G := by
    have hF := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace F)
      (μ := Measure.pi (fun _ : κ => AddCircle.haarAddCircle))
    have hG := G.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace G)
      (μ := Measure.pi (fun _ : κ => AddCircle.haarAddCircle))
    simp only [ContinuousMap.add_apply, finiteComplexSetMean, Finset.sum_add_distrib,
      add_div, integral_add hF hG]
    ring
  map_smul' c F := by
    simp only [ContinuousMap.smul_apply, finiteComplexSetMean, ← Finset.smul_sum,
      smul_div_assoc, integral_smul, smul_sub, RingHom.id_apply]

theorem unit_torus_finite_discrepancy_norm_bound {κ α : Type*} [Fintype κ]
    (s : Finset α) (f : α → UnitAddTorus κ) (F : C(UnitAddTorus κ, ℂ)) :
    ‖unitTorusFiniteDiscrepancy s f F‖ ≤ 2*‖F‖ := by
  have hm := finiteComplexSetMean_norm_bound s (fun a => F (f a)) ‖F‖ (norm_nonneg F)
    (fun a _ => F.norm_coe_le_norm _)
  have hi : ‖∫ t, F t ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle)‖ ≤ ‖F‖ := by
    simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : κ => AddCircle.haarAddCircle))
        (Filter.Eventually.of_forall (fun t => F.norm_coe_le_norm t))
  exact (norm_sub_le _ _).trans (by linarith only [hm, hi])

theorem unit_torus_finite_nonzero_fourier_discrepancy {κ α : Type*} [Fintype κ]
    (s : Finset α) (f : α → UnitAddTorus κ) (k : κ → ℤ) (hk : k ≠ 0) :
    unitTorusFiniteDiscrepancy s f (UnitAddTorus.mFourier k) =
      finiteComplexSetMean s (fun a => UnitAddTorus.mFourier k (f a)) := by
  change _-∫ t, UnitAddTorus.mFourier k t ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle) = _
  rw [unit_torus_fourier_haar_integral, if_neg hk, sub_zero]

theorem unit_torus_finite_zero_fourier_discrepancy {κ α : Type*} [Fintype κ]
    (s : Finset α) (hs : s.Nonempty) (f : α → UnitAddTorus κ) :
    unitTorusFiniteDiscrepancy s f (UnitAddTorus.mFourier (0 : κ → ℤ)) = 0 := by
  change finiteComplexSetMean s (fun a => UnitAddTorus.mFourier (0 : κ → ℤ) (f a))-
    ∫ t, UnitAddTorus.mFourier (0 : κ → ℤ) t ∂Measure.pi (fun _ : κ => AddCircle.haarAddCircle) = 0
  rw [unit_torus_fourier_haar_integral, if_pos rfl]
  simp only [UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, finiteComplexSetMean,
    Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [div_self (by exact_mod_cast hs.card_pos.ne'), sub_self]

theorem unit_torus_finite_fourier_large_frequency {κ α : Type*} [Fintype κ]
    (s : Finset α) (hs : s.Nonempty) (f : α → UnitAddTorus κ) (c : (κ → ℤ) →₀ ℂ)
    (B δ : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hbudget : ∑ k ∈ c.support, ‖c k‖ ≤ B)
    (hlarge : δ/2 ≤ ‖unitTorusFiniteDiscrepancy s f
      (c.sum (fun k a => a • (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ))))‖) :
    ∃ k ∈ c.support, k ≠ 0 ∧ δ/(4*B) ≤ ‖unitTorusFiniteDiscrepancy s f (UnitAddTorus.mFourier k)‖ := by
  by_contra! h
  have hmode : ∀ k ∈ c.support, ‖unitTorusFiniteDiscrepancy s f (UnitAddTorus.mFourier k)‖ ≤ δ/(4*B) := by
    intro k hk
    by_cases hz : k=0
    · rw [hz, unit_torus_finite_zero_fourier_discrepancy s hs f, norm_zero]
      positivity
    · exact (h k hk hz).le
  have heq : unitTorusFiniteDiscrepancy s f
      (c.sum (fun k a => a • (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ)))) =
      ∑ k ∈ c.support, c k*unitTorusFiniteDiscrepancy s f (UnitAddTorus.mFourier k) := by
    rw [Finsupp.sum, map_sum]
    simp only [map_smul, smul_eq_mul]
  have hb : ‖unitTorusFiniteDiscrepancy s f
      (c.sum (fun k a => a • (UnitAddTorus.mFourier k : C(UnitAddTorus κ, ℂ))))‖ ≤ δ/4 := by
    rw [heq]
    calc
      _ ≤ ∑ k ∈ c.support, ‖c k*unitTorusFiniteDiscrepancy s f (UnitAddTorus.mFourier k)‖ := norm_sum_le _ _
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
