import Hindman168.AlignmentIntervalMeans

namespace Hindman168
open scoped Classical

theorem alignment_forward_interval_difference (A B A' B' : ℤ) (D : ℕ)
    (hA : A ≤ A' ∧ A' ≤ A + D) (hB : B ≤ B' ∧ B' ≤ B + D) :
    (Finset.Ico A B \ Finset.Ico A' B').card ≤ D ∧
      (Finset.Ico A' B' \ Finset.Ico A B).card ≤ D := by
  have hleft : Finset.Ico A B \ Finset.Ico A' B' ⊆ Finset.Ico A (A + D) := by
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_Ico] at hz ⊢
    omega
  have hright : Finset.Ico A' B' \ Finset.Ico A B ⊆ Finset.Ico B (B + D) := by
    intro z hz
    simp only [Finset.mem_sdiff, Finset.mem_Ico] at hz ⊢
    omega
  constructor
  · simpa only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using Finset.card_le_card hleft
  · simpa only [Int.card_Ico, add_sub_cancel_left, Int.toNat_natCast] using Finset.card_le_card hright

theorem alignment_forward_interval_mean_error (A B A' B' : ℤ) (D : ℕ)
    (hAB : A < B) (hA : A ≤ A' ∧ A' ≤ A + D) (hB : B ≤ B' ∧ B' ≤ B + D)
    (f : ℤ → ℂ) (K : ℝ) (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (Finset.Ico A B) f - finiteComplexSetMean (Finset.Ico A' B') f‖ ≤
      4 * K * D / ((B : ℝ) - A) := by
  have hc := alignment_forward_interval_difference A B A' B' D hA hB
  have hl : ((Finset.Ico A B).card : ℝ) = (B : ℝ) - A := by
    rw [Int.card_Ico]
    exact_mod_cast Int.toNat_of_nonneg (sub_nonneg.mpr hAB.le)
  have hs : (Finset.Ico A B).Nonempty := Finset.nonempty_Ico.mpr hAB
  have hh := finiteComplexSetMean_difference_bound (Finset.Ico A B) (Finset.Ico A' B') hs f K hK hf
  rw [hl] at hh
  apply hh.trans
  apply div_le_div_of_nonneg_right _ (by exact_mod_cast sub_nonneg.mpr hAB.le)
  have h₁ : ((Finset.Ico A B \ Finset.Ico A' B').card : ℝ) ≤ D := by exact_mod_cast hc.1
  have h₂ : ((Finset.Ico A' B' \ Finset.Ico A B).card : ℝ) ≤ D := by exact_mod_cast hc.2
  nlinarith

theorem alignment_endpoint_unrestricted_mean_error (A B r : ℤ) (d : ℕ)
    (hd : 0 < d) (hAB : A < B) (f : ℤ → ℂ) (K : ℝ) (hK : 0 ≤ K)
    (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖finiteComplexSetMean (Finset.Ico A B) f -
      finiteComplexSetMean (Finset.Ico (alignmentResidueEndpoint A d r)
        (alignmentResidueEndpoint B d r)) f‖ ≤ 4 * K * d / ((B : ℝ) - A) := by
  have hA := alignmentResidueEndpoint_bounds A d r (by exact_mod_cast hd)
  have hB := alignmentResidueEndpoint_bounds B d r (by exact_mod_cast hd)
  exact alignment_forward_interval_mean_error A B _ _ d hAB ⟨hA.1, hA.2.le⟩ ⟨hB.1, hB.2.le⟩ f K hK hf

end Hindman168
