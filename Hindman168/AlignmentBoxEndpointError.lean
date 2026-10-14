import Hindman168.UniformBoxMassComparison
import Hindman168.AlignmentEndpointMeanError

namespace Hindman168
open scoped BigOperators Classical

theorem alignment_forward_box_mean_error {ι : Type*} [Fintype ι]
    (L U L' U' : ι → ℤ) (D : ℕ) (hLU : ∀ j, L j < U j) (hLU' : ∀ j, L' j < U' j)
    (hL : ∀ j, L j ≤ L' j ∧ L' j ≤ L j + D)
    (hU : ∀ j, U j ≤ U' j ∧ U' j ≤ U j + D)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (L j) (U j))) f -
      finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (L' j) (U' j))) f‖ ≤
      ∑ j, 4 * K * D / ((U j : ℝ) - L j) := by
  apply (FiniteMass.finiteComplexBoxMean_difference_bound _ _
    (fun j => Finset.nonempty_Ico.mpr (hLU j))
    (fun j => Finset.nonempty_Ico.mpr (hLU' j)) f K hK hf).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have hc := alignment_forward_interval_difference (L j) (U j) (L' j) (U' j) D (hL j) (hU j)
  have hcard : ((Finset.Ico (L j) (U j)).card : ℝ) = (U j : ℝ) - L j := by
    rw [Int.card_Ico]
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hLU j).le)
  rw [hcard, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast sub_nonneg.mpr (hLU j).le)
  have h1 : (((Finset.Ico (L j) (U j)) \ (Finset.Ico (L' j) (U' j))).card : ℝ) ≤ D := by
    exact_mod_cast hc.1
  have h2 : (((Finset.Ico (L' j) (U' j)) \ (Finset.Ico (L j) (U j))).card : ℝ) ≤ D := by
    exact_mod_cast hc.2
  have hh := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK
  nlinarith [hh]

theorem alignment_endpoint_box_mean_error {ι : Type*} [Fintype ι]
    (L U r : ι → ℤ) (d : ℕ) (hd : 0 < d) (hlen : ∀ j, 2 * (d : ℤ) ≤ U j - L j)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (L j) (U j))) f -
      finiteComplexSetMean (Fintype.piFinset (fun j =>
        Finset.Ico (alignmentResidueEndpoint (L j) d (r j))
          (alignmentResidueEndpoint (U j) d (r j)))) f‖ ≤
      ∑ j, 4 * K * d / ((U j : ℝ) - L j) := by
  have hdZ : (0 : ℤ) < d := by exact_mod_cast hd
  have hl (j : ι) := alignmentResidueEndpoint_bounds (L j) d (r j) hdZ
  have hu (j : ι) := alignmentResidueEndpoint_bounds (U j) d (r j) hdZ
  apply alignment_forward_box_mean_error L U _ _ d
    (fun j => by have := hlen j; omega)
    (fun j => by have := hlen j; have := hl j; have := hu j; omega)
    (fun j => ⟨(hl j).1, (hl j).2.le⟩) (fun j => ⟨(hu j).1, (hu j).2.le⟩) f K hK hf

end Hindman168
