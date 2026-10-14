import Hindman168.AlignmentClassCounts
import Hindman168.AlignmentCubeStepRatio

namespace Hindman168
open Filter
open scoped Topology BigOperators

theorem alignment_interval_class_relative_count (L U r : ℤ) (q : ℕ)
    (hq : 0 < q) (hLU : L < U) :
    |((alignmentIntervalClass L U q r).card : ℝ) * q / ((U : ℝ) - L) - 1| ≤
      (q : ℝ) / ((U : ℝ) - L) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hlen : (0 : ℝ) < (U : ℝ) - L := by exact_mod_cast sub_pos.mpr hLU
  have hc := alignment_interval_class_count L U r q hq hLU.le
  have he : ((alignmentIntervalClass L U q r).card : ℝ) * q / ((U : ℝ) - L) - 1 =
      (((alignmentIntervalClass L U q r).card : ℝ) - ((U : ℝ) - L) / q) *
        ((q : ℝ) / ((U : ℝ) - L)) := by
    field_simp
  rw [he, abs_mul, abs_of_pos (div_pos hqR hlen)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hc (div_pos hqR hlen).le

theorem alignment_actual_class_count_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    (c eps : ℝ) (hc : 0 < c) (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U r : ℤ,
      c * alignmentCubeScale F w i T x ≤ (U : ℝ) - L →
      (alignmentIntervalClass L U (d * alignmentNaturalBlockProduct x T : ℕ) r).Nonempty ∧
      |((alignmentIntervalClass L U (d * alignmentNaturalBlockProduct x T : ℕ) r).card : ℝ) *
          (d * alignmentNaturalBlockProduct x T : ℕ) / ((U : ℝ) - L) - 1| ≤ eps := by
  have hdelta : 0 < min (c / 2) (eps * c) := lt_min (by positivity) (by positivity)
  filter_upwards [alignment_actual_step_eventually_small hF i T d hdelta] with w hw x hx L U r hlen
  have hq : 0 < d * alignmentNaturalBlockProduct x T := Nat.mul_pos hd (Finset.prod_pos hx)
  have hqR : (0 : ℝ) < (d * alignmentNaturalBlockProduct x T : ℕ) := by exact_mod_cast hq
  have hz : 0 ≤ alignmentCubeScale F w i T x := by
    unfold alignmentCubeScale alignmentShortBinVolume
    positivity
  have hs : ((d * alignmentNaturalBlockProduct x T : ℕ) : ℝ) ≤
      min (c / 2) (eps * c) * alignmentCubeScale F w i T x := by
    simpa only [Nat.cast_mul] using hw x hx
  have hhalf := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hz)
  have hfull := hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hz)
  have h2 : 2 * ((d * alignmentNaturalBlockProduct x T : ℕ) : ℝ) ≤ (U : ℝ) - L := by
    nlinarith
  have h2Z : 2 * (d * alignmentNaturalBlockProduct x T : ℕ) ≤ U - L := by exact_mod_cast h2
  have hLU : L < U := by
    have hp : (0 : ℝ) < (U : ℝ) - L := by linarith
    exact_mod_cast sub_pos.mp hp
  refine ⟨alignment_interval_class_nonempty L U r _ hq h2Z, ?_⟩
  apply (alignment_interval_class_relative_count L U r _ hq hLU).trans
  apply (div_le_iff₀ (by exact_mod_cast sub_pos.mpr hLU)).mpr
  nlinarith [mul_le_mul_of_nonneg_left hlen heps.le]

end Hindman168
