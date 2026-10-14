import Hindman168.ComplexMassTranslation

namespace Hindman168
open FiniteMass
open scoped BigOperators Classical

theorem uniformIntervalMass_eq_Ico (L U : ℤ) (hLU : L ≤ U) :
    uniformIntervalMass L (U - L).toNat = uniformFinsetMass (Finset.Ico L U) := by
  unfold uniformIntervalMass integerWindow
  rw [Int.toNat_of_nonneg (sub_nonneg.mpr hLU), add_sub_cancel]

theorem complex_box_translation_bound {ι : Type*} [Fintype ι]
    (L U u : ι → ℤ) (hLU : ∀ j, L j < U j)
    (f : (ι → ℤ) → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (L j) (U j)))
        (fun z => f (fun j => z j + u j)) -
      finiteComplexSetMean (Fintype.piFinset (fun j => Finset.Ico (L j) (U j))) f‖ ≤
      K * ∑ j, 2 * |(u j : ℝ)| / ((U j : ℝ) - L j) := by
  have hp (j : ι) : 0 < (U j - L j).toNat := by have := hLU j; omega
  have hm (j : ι) := uniformIntervalMass_eq_Ico (L j) (U j) (hLU j).le
  have h := piMass_translation_complex_bound (fun j => uniformIntervalMass (L j) (U j - L j).toNat)
    u f K (fun j => uniformIntervalMass_nonneg _ _) (fun j => uniformIntervalMass_total _ (hp j)) hK hf
  simp_rw [hm] at h
  rw [← uniformFinsetMass_pi, complexExpectation_uniformFinset, complexExpectation_uniformFinset] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ hK
  apply Finset.sum_le_sum
  intro j _
  have hb := uniform_interval_translation_linear (L j) (hp j) (u j)
  have hn : ((U j - L j).toNat : ℝ) = (U j : ℝ) - L j := by
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr (hLU j).le)
  simpa only [hm, hn] using hb

end Hindman168
