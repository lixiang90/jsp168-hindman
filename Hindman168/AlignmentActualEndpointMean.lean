import Hindman168.AlignmentEndpointMeanError
import Hindman168.AlignmentCubeStepRatio

namespace Hindman168
open Filter
open scoped Topology BigOperators

theorem alignment_actual_endpoint_mean_eventually
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (d : ℕ) (hd : 0 < d)
    (c K eps : ℝ) (hc : 0 < c) (hK : 0 < K) (heps : 0 < eps) :
    ∀ᶠ w in atTop, ∀ x : Fin n → ℕ, (∀ j ∈ T, 0 < x j) → ∀ L U r : ℤ,
      c * alignmentCubeScale F w i T x ≤ (U : ℝ) - L →
      ∀ f : ℤ → ℂ, (∀ z, ‖f z‖ ≤ K) →
      ‖finiteComplexSetMean (Finset.Ico L U) f -
        finiteComplexSetMean (Finset.Ico
          (alignmentResidueEndpoint L (d * alignmentNaturalBlockProduct x T : ℕ) r)
          (alignmentResidueEndpoint U (d * alignmentNaturalBlockProduct x T : ℕ) r)) f‖ ≤ eps := by
  have hdelta : 0 < eps * c / (4 * K) := by positivity
  filter_upwards [alignment_actual_step_eventually_small hF i T d hdelta,
    master_microcell_eventually_positive hF (fun _ => i)] with w hw hR x hx L U r hlen f hf
  have ht : 0 < alignmentNaturalBlockProduct x T := Finset.prod_pos hx
  have hz : 0 < alignmentCubeScale F w i T x := by
    unfold alignmentCubeScale alignmentShortBinVolume
    have hm : (0 : ℝ) < (F.modulus w : ℕ) := by exact_mod_cast (F.modulus w).pos
    have hR' : (0 : ℝ) < alignedSqrtMicrocellWidth (F.gap w i.val) (F.modulus w) := by exact_mod_cast hR
    positivity
  have hLU : (L : ℝ) < U := by nlinarith
  have hLUZ : L < U := by exact_mod_cast hLU
  have herr := alignment_endpoint_unrestricted_mean_error L U r
    (d * alignmentNaturalBlockProduct x T) (Nat.mul_pos hd ht) hLUZ f K hK.le hf
  apply herr.trans
  apply (div_le_iff₀ (sub_pos.mpr hLU)).mpr
  have hb : (d : ℝ) * alignmentNaturalBlockProduct x T * (4 * K) ≤
      eps * c * alignmentCubeScale F w i T x := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * K)).mp
    simpa only [div_mul_eq_mul_div] using hw x hx
  rw [Nat.cast_mul]
  nlinarith [mul_le_mul_of_nonneg_left hlen heps.le]

end Hindman168
