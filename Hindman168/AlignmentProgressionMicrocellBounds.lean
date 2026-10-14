import Hindman168.AlignmentNumericalPolynomialBounds
import Hindman168.AlignmentSlotMicrocellBounds
import Hindman168.AlignmentIntegerArrayArguments

/-! Uniform smallness of the literal scaled array progression, for all
earlier values in their cutoffs and all canonical residue/shift data. -/

namespace Hindman168

open Filter
open scoped BigOperators Topology Classical

theorem alignmentIntegerArrayProgression_scaled_bound {n : ℕ} {i : Fin n}
    (M : ℕ) (Δ : AlignmentAddingPair n i → ℤ) (T : Finset (Fin n))
    (u : AlignmentAddingPair n i → ℤ) {L : ℤ} (hL : 0 ≤ L)
    (hΔ : ∀ e, |(M : ℤ) * Δ e| ≤ L) :
    |(M : ℤ) * alignmentIntegerArrayProgression Δ T u| ≤ L * alignmentIntegerSlotWeight u := by
  letI := alignmentAddingPairFintype n i
  unfold alignmentIntegerArrayProgression alignmentIntegerSlotWeight
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ e, |(M : ℤ) * (if e.targetTail = T then u e * Δ e else 0)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ e, L * |u e| := by
      apply Finset.sum_le_sum
      intro e _
      by_cases he : e.targetTail = T
      · rw [if_pos he]
        have hr : (M : ℤ) * (u e * Δ e) = u e * ((M : ℤ) * Δ e) := by ring
        rw [hr, abs_mul]
        simpa only [mul_comm L] using mul_le_mul_of_nonneg_left (hΔ e) (abs_nonneg (u e))
      · simp only [if_neg he, mul_zero, abs_zero]
        exact mul_nonneg hL (abs_nonneg _)
    _ = _ := (Finset.mul_sum _ _ _).symm

theorem alignment_progression_microcell_uniform_small
    {d n : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions n A D F) (i : Fin n) (q₀ : ℕ)
    (U : Finset (AlignmentAddingPair n i → ℤ)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ w in atTop, ∀ u ∈ U, ∀ t : Fin n → ℕ,
      (∀ j, j < i → t j ≤ F.cutoff w j.val ^ 2) →
      ∀ ρ : AlignmentAddingPair n i → ℕ, (∀ e, ρ e ≤ (F.modulus w : ℕ) ^ 2) →
      ∀ Δ : AlignmentAddingPair n i → ℤ,
      (∀ e, (F.modulus w : ℤ) * Δ e = (alignmentIntegerNumerator q₀ w e t : ℤ) -
        (alignmentNaturalBlockProduct t e.targetTail : ℤ) * ρ e) →
      ∀ T : Finset (Fin n), |((F.modulus w : ℤ) * alignmentIntegerArrayProgression Δ T u : ℝ)| ≤
        ε * alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by
  apply (eventually_all_finset U).mpr
  intro u _
  filter_upwards [master_microcell_eventually_polynomial_small hF (fun _ => i) 3
    (2 * (alignmentIntegerSlotWeight u : ℝ)) hε] with w hw
  intro t ht ρ hρ Δ hexact T
  have hb := alignmentIntegerArrayProgression_scaled_bound (F.modulus w) Δ T u
    (L := 2 * (F.auxiliary w i.val : ℤ) ^ 3) (by positivity)
    (fun e => alignmentProgressionShift_polynomial_bound hF q₀ w t ht e (ρ e) (hρ e) (Δ e) (hexact e))
  have hbR : |((F.modulus w : ℤ) * alignmentIntegerArrayProgression Δ T u : ℝ)| ≤
      (2 * (F.auxiliary w i.val : ℝ) ^ 3) * (alignmentIntegerSlotWeight u : ℝ) := by exact_mod_cast hb
  have he : (2 * (F.auxiliary w i.val : ℝ) ^ 3) * (alignmentIntegerSlotWeight u : ℝ) =
      (2 * (alignmentIntegerSlotWeight u : ℝ)) * (F.auxiliary w i.val : ℝ) ^ 3 := by ring
  exact (hbR.trans_eq he).trans hw

end Hindman168
