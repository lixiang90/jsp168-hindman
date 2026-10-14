import Hindman168.AlignmentBoxEndpointError
import Hindman168.AlignmentCubeStepRatio

namespace Hindman168
open Filter
open scoped Topology BigOperators Classical

theorem alignment_actual_box_endpoint_error_eventually
    {ι : Type*} [Fintype ι] {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    (c K eps : ℝ) (hc : 0 < c) (hK : 0 ≤ K) (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) →
      ∀ L U r : ι → ℤ, (∀ j, c * alignmentCubeScale F w i T x ≤ (U j : ℝ) - L j) →
      ∀ f : (ι → ℤ) → ℂ, (∀ z, ‖f z‖ ≤ K) →
      let q : ℕ := d * alignmentNaturalBlockProduct x T
      ‖finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (L j) (U j))) f -
        finiteComplexSetMean (Fintype.piFinset (fun j =>
          Finset.Ico (alignmentResidueEndpoint (L j) q (r j))
            (alignmentResidueEndpoint (U j) q (r j)))) f‖ ≤ eps := by
  let eta := eps / ((Fintype.card ι : ℝ) + 1)
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hden : 0 < 4 * (K + 1) := by positivity
  have hdelta : 0 < min (c / 2) (eta * c / (4 * (K + 1))) := by positivity
  filter_upwards [alignment_actual_step_eventually_small hF i T d hdelta]
    with w hw x hx L U r hlen f hf
  let q : ℕ := d * alignmentNaturalBlockProduct x T
  have hq : 0 < q := Nat.mul_pos hd (Finset.prod_pos hx)
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hz : 0 ≤ alignmentCubeScale F w i T x := by
    unfold alignmentCubeScale alignmentShortBinVolume
    positivity
  have hs : (q : ℝ) ≤ min (c / 2) (eta * c / (4 * (K + 1))) * alignmentCubeScale F w i T x := by
    simpa only [q, Nat.cast_mul] using hw x hx
  have hhalf := hs.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hz)
  have hfull := hs.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hz)
  rw [div_mul_eq_mul_div, le_div_iff₀ hden] at hfull
  have h2 (j : ι) : 2 * (q : ℤ) ≤ U j - L j := by
    have hr : 2 * (q : ℝ) ≤ (U j : ℝ) - L j := by nlinarith [hlen j]
    exact_mod_cast hr
  have hb := alignment_endpoint_box_mean_error L U r q hq h2 f K hK hf
  apply hb.trans
  calc
    _ ≤ ∑ _j : ι, eta := by
      apply Finset.sum_le_sum
      intro j _
      have hpos : (0 : ℝ) < (U j : ℝ) - L j := by nlinarith [hlen j]
      apply (div_le_iff₀ hpos).mpr
      have ht := mul_le_mul_of_nonneg_left (hlen j) heta.le
      nlinarith
    _ ≤ eps := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      dsimp [eta]
      rw [← mul_div_assoc]
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith

end Hindman168
