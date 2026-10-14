import Hindman168.FinitePositiveLagDensity

/-! Dense genuine derivative means on their actual remaining intervals.
No zero-extended sample is identified with an untruncated orbit sample. -/
namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_dense_derivative_means (f : ℕ → ℂ) (N : ℕ) (hN : 0 < N)
    (hf : ∀ n < N, ‖f n‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : 4 ≤ δ^2*(N : ℝ))
    (hmean : δ ≤ ‖finiteComplexSetMean (Finset.range N) f‖) :
    ∃ T : Finset ℕ, δ^2/8*(N : ℝ) ≤ T.card ∧
      ∀ h ∈ T, 0 < h ∧ h < N ∧ 0 < N-h ∧ δ^2/8*(N : ℝ) ≤ (N-h : ℕ) ∧
        δ^2/8 ≤ ‖finiteComplexSetMean (Finset.range (N-h))
          (fun n => f (n+h)*star (f n))‖ := by
  let T := (positiveNaturalLags N).filter (fun h => δ^2/8*(N : ℝ) ≤
    ‖finiteComplexLagCorrelation f N h‖)
  refine ⟨T,finite_complex_positive_lag_density f N hN hf δ hδ hlarge hmean,?_⟩
  intro h hh
  have hm := Finset.mem_filter.mp hh
  have hp := (positive_natural_lags_mem N h).mp hm.1
  obtain ⟨hr,hlen,hcorr⟩ := finite_complex_large_lag_remaining_mean f N h hf hN
    (δ^2/8) (by positivity) hm.2
  exact ⟨hp.2,hp.1,hr,hlen,hcorr⟩

theorem finite_complex_Ico_nat_mean (N : ℕ) (f : ℤ → ℂ) :
    finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) f =
      finiteComplexSetMean (Finset.range N) (fun n => f n) := by
  have he : Finset.Ico 0 (N : ℤ) = (Finset.range N).image (fun n : ℕ => (n : ℤ)) := by
    ext z
    simp only [Finset.mem_Ico,Finset.mem_image,Finset.mem_range]
    constructor
    · rintro ⟨hz,hzN⟩
      refine ⟨z.toNat,?_,Int.toNat_of_nonneg hz⟩
      omega
    · rintro ⟨n,hn,rfl⟩
      exact ⟨Nat.cast_nonneg _,by exact_mod_cast hn⟩
  rw [he]
  exact finiteComplexSetMean_image _ _ Nat.cast_injective f

theorem finite_complex_dense_integer_derivative_means (f : ℤ → ℂ) (N : ℕ) (hN : 0 < N)
    (hf : ∀ n : ℤ, 0 ≤ n → n < N → ‖f n‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hlarge : 4 ≤ δ^2*(N : ℝ))
    (hmean : δ ≤ ‖finiteComplexSetMean (Finset.Ico 0 (N : ℤ)) f‖) :
    ∃ T : Finset ℕ, δ^2/8*(N : ℝ) ≤ T.card ∧
      ∀ h ∈ T, 0 < h ∧ h < N ∧ 0 < N-h ∧ δ^2/8*(N : ℝ) ≤ (N-h : ℕ) ∧
        δ^2/8 ≤ ‖finiteComplexSetMean (Finset.Ico 0 ((N-h : ℕ) : ℤ))
          (fun n => f (n+h)*star (f n))‖ := by
  rw [finite_complex_Ico_nat_mean] at hmean
  obtain ⟨T,hT,hcorr⟩ := finite_complex_dense_derivative_means (fun n => f n) N hN
    (fun n hn => hf n (Nat.cast_nonneg _) (by exact_mod_cast hn)) δ hδ hlarge hmean
  refine ⟨T,hT,?_⟩
  intro h hh
  obtain ⟨hpos,hlt,hr,hlen,hm⟩ := hcorr h hh
  refine ⟨hpos,hlt,hr,hlen,?_⟩
  simpa only [finite_complex_Ico_nat_mean,Nat.cast_add] using hm

end Hindman168
