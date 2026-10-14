import Hindman168.PositivePrincipalSumBounds
import Mathlib.Order.LiminfLimsup

/-!
# Choosing the tolerances before constructing the models

The constants depend only on the finite calibration/count catalogue and
the positive alignment mass. They do not depend on model complexity.
-/

namespace Hindman168
open Filter
open scoped Topology

/-- The strict numerical budget used in the final counting proof can
always be met with a positive calibration threshold below one quarter
and a single positive prediction tolerance. -/
theorem positivePrincipalSum_choose_tolerances (C K q : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ θ η : ℝ, 0 < θ ∧ θ < 1/4 ∧ 0 < η ∧
      0 < θ ^ q * (δ - (C : ℝ) * (3*θ + η)) - (K : ℝ) * η := by
  have hC : (0 : ℝ) ≤ C := Nat.cast_nonneg _
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hdenC : 0 < 12 * ((C : ℝ) + 1) := by positivity
  have hmin : 0 < min (1/4 : ℝ) (δ / (12 * ((C : ℝ) + 1))) :=
    lt_min (by norm_num) (div_pos hδ hdenC)
  obtain ⟨θ, hθ, hθbound⟩ := exists_between hmin
  have hθsmall : θ < (1/4 : ℝ) := hθbound.trans_le (min_le_left _ _)
  have hθC := (lt_div_iff₀ hdenC).mp (hθbound.trans_le (min_le_right _ _))
  have ht : 0 < θ ^ q := pow_pos hθ _
  have hdenC' : 0 < 4 * ((C : ℝ) + 1) := by positivity
  have hdenK : 0 < 4 * ((K : ℝ) + 1) := by positivity
  have hminη : 0 < min (δ / (4 * ((C : ℝ) + 1)))
      (δ * θ ^ q / (4 * ((K : ℝ) + 1))) :=
    lt_min (div_pos hδ hdenC') (div_pos (mul_pos hδ ht) hdenK)
  obtain ⟨η, hη, hηbound⟩ := exists_between hminη
  have hηC := (lt_div_iff₀ hdenC').mp (hηbound.trans_le (min_le_left _ _))
  have hηK := (lt_div_iff₀ hdenK).mp (hηbound.trans_le (min_le_right _ _))
  refine ⟨θ, η, hθ, hθsmall, hη, ?_⟩
  have hbad : (C : ℝ) * (3*θ + η) < δ / 2 := by nlinarith
  have herr : (K : ℝ) * η < δ * θ ^ q / 4 := by nlinarith
  nlinarith [mul_pos ht (sub_pos.mpr hbad)]

/-- The ordinary liminf bound in Principle 2.4 gives a fixed positive
lower bound along the same cofinal ultrafilter used by prediction. -/
theorem positivePrincipalSum_alignment_liminf {α : Type*}
    (μ : ℕ → FiniteMass.Mass α) (E : ℕ → α → Prop)
    (hμ : ∀ᶠ w in atTop, ∀ x, 0 ≤ μ w x)
    (δ : ℝ) (hδ : 0 < δ)
    (hmass : δ ≤ Filter.liminf (fun w => FiniteMass.event (μ w) (E w)) atTop)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop) :
    ∀ᶠ w in (U : Filter ℕ), δ / 2 ≤ FiniteMass.event (μ w) (E w) := by
  have hb : IsBoundedUnder (· ≥ ·) atTop (fun w => FiniteMass.event (μ w) (E w)) :=
    isBoundedUnder_of_eventually_ge (hμ.mono (fun w hw => FiniteMass.event_nonneg _ _ hw))
  have he := eventually_lt_of_lt_liminf
    ((show δ / 2 < δ by linarith).trans_le hmass) hb
  exact (he.mono (fun _ h => h.le)).filter_mono hU

end Hindman168
