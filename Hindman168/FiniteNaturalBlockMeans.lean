import Hindman168.FiniteNaturalBlockReindex
import Hindman168.FiniteComplexSetMean

namespace Hindman168
open scoped BigOperators Classical

theorem finite_complex_set_mean_exists_norm_ge {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (f : α → ℂ) : ∃ a ∈ s, ‖finiteComplexSetMean s f‖ ≤ ‖f a‖ := by
  obtain ⟨a, ha, hmax⟩ := Finset.exists_max_image s (fun a => ‖f a‖) hs
  exact ⟨a, ha, finiteComplexSetMean_norm_bound s f ‖f a‖ (norm_nonneg _)
    (fun b hb => hmax b hb)⟩

theorem finite_natural_progression_blocks_mean (K q H : ℕ) (f : ℕ → ℂ) :
    finiteComplexSetMean (Finset.range (q*H*K)) f =
      finiteComplexSetMean (Finset.range K) (fun b =>
        finiteComplexSetMean (Finset.range q) (fun r =>
          finiteComplexSetMean (Finset.range H) (fun j => f (q*H*b+r+q*j)))) := by
  simp only [finiteComplexSetMean, Finset.card_range, div_eq_mul_inv, ← Finset.sum_mul]
  rw [finite_natural_progression_blocks_sum]
  simp only [Nat.cast_mul, mul_inv_rev]
  ring

/-- A genuine large mean retains a large mean on an actual sufficiently
long prefix, with no assumed localization existence. -/
theorem finite_complex_prefix_mean_large (f : ℕ → ℂ) (N P : ℕ) (hN : 0 < N)
    (hPN : P ≤ N) (hf : ∀ n < N, ‖f n‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (htail : ((N-P : ℕ) : ℝ) ≤ δ*(N : ℝ)/4)
    (hmean : δ ≤ ‖finiteComplexSetMean (Finset.range N) f‖) :
    0 < P ∧ δ/2 ≤ ‖finiteComplexSetMean (Finset.range P) f‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hPbound : ‖∑ n ∈ Finset.range P, f n‖ ≤ (P : ℝ) := by
    simpa only [Finset.card_range, mul_one] using
      finite_complex_sum_norm_bound (Finset.range P) f 1
        (fun n hn => hf n ((Finset.mem_range.mp hn).trans_le hPN))
  have hTbound : ‖∑ j ∈ Finset.range (N-P), f (P+j)‖ ≤ (N-P : ℕ) := by
    simpa only [Finset.card_range, mul_one] using
      finite_complex_sum_norm_bound (Finset.range (N-P)) (fun j => f (P+j)) 1
        (fun j hj => hf (P+j) (by have hj' := Finset.mem_range.mp hj; omega))
  have hsum : (∑ n ∈ Finset.range N, f n) =
      (∑ n ∈ Finset.range P, f n)+(∑ j ∈ Finset.range (N-P), f (P+j)) := by
    have he := Finset.sum_range_add f P (N-P)
    rw [Nat.add_sub_of_le hPN] at he
    exact he
  have hwhole : δ*(N : ℝ) ≤ ‖∑ n ∈ Finset.range N, f n‖ := by
    rw [finiteComplexSetMean, norm_div, Complex.norm_natCast, Finset.card_range] at hmean
    exact (le_div_iff₀ hNr).mp hmean
  have htriangle : ‖∑ n ∈ Finset.range N, f n‖ ≤
      ‖∑ n ∈ Finset.range P, f n‖+(N-P : ℕ) := by
    rw [hsum]
    exact (norm_add_le _ _).trans (add_le_add le_rfl hTbound)
  have hPr : (0 : ℝ) < P := by
    nlinarith [mul_pos hδ hNr]
  have hP : 0 < P := by exact_mod_cast hPr
  refine ⟨hP, ?_⟩
  rw [finiteComplexSetMean, norm_div, Complex.norm_natCast, Finset.card_range]
  apply (le_div_iff₀ hPr).mpr
  have hPNr : (P : ℝ) ≤ N := by exact_mod_cast hPN
  have hmul := mul_le_mul_of_nonneg_left hPNr hδ.le
  nlinarith

/-- Select an actual short arithmetic progression from a true large mean.
The sample positions and the discarded tail are original integer indices. -/
theorem finite_complex_short_progression_mean_large (f : ℕ → ℂ) (N q H : ℕ)
    (hN : 0 < N) (hq : 0 < q) (hH : 0 < H)
    (hf : ∀ n < N, ‖f n‖ ≤ 1) (δ : ℝ) (hδ : 0 < δ)
    (hwidth : 4*(q : ℝ)*(H : ℝ) ≤ δ*(N : ℝ))
    (hmean : δ ≤ ‖finiteComplexSetMean (Finset.range N) f‖) :
    ∃ a : ℕ, a < N ∧ (∀ j < H, a+q*j < N) ∧
      δ/2 ≤ ‖finiteComplexSetMean (Finset.range H) (fun j => f (a+q*j))‖ := by
  let K := N/(q*H)
  let P := q*H*K
  have hPN : P ≤ N := by simpa only [P, K, Nat.mul_comm] using Nat.div_mul_le_self N (q*H)
  have hmod : N-P = N%(q*H) := by
    have hm := Nat.mod_add_div N (q*H)
    dsimp only [P, K]
    omega
  have htail : ((N-P : ℕ) : ℝ) ≤ δ*(N : ℝ)/4 := by
    rw [hmod]
    have ht : ((N%(q*H) : ℕ) : ℝ) ≤ (q : ℝ)*(H : ℝ) := by
      exact_mod_cast (Nat.mod_lt N (Nat.mul_pos hq hH)).le
    linarith
  obtain ⟨hP, hprefix⟩ := finite_complex_prefix_mean_large f N P hN hPN hf δ hδ htail hmean
  have hK : 0 < K := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hh : 0 < q*H*K := hP
    rw [hz, mul_zero] at hh
    exact (Nat.lt_irrefl 0) hh
  rw [show P=q*H*K from rfl, finite_natural_progression_blocks_mean] at hprefix
  obtain ⟨b, hb, hmb⟩ := finite_complex_set_mean_exists_norm_ge (Finset.range K)
    (Finset.nonempty_range_iff.mpr hK.ne')
    (fun b => finiteComplexSetMean (Finset.range q) (fun r =>
      finiteComplexSetMean (Finset.range H) (fun j => f (q*H*b+r+q*j))))
  obtain ⟨r, hr, hmr⟩ := finite_complex_set_mean_exists_norm_ge (Finset.range q)
    (Finset.nonempty_range_iff.mpr hq.ne')
    (fun r => finiteComplexSetMean (Finset.range H) (fun j => f (q*H*b+r+q*j)))
  have hindex : ∀ j < H, q*H*b+r+q*j < N := by
    intro j hj
    exact (natural_progression_block_index_bound K q H b r j
      (Finset.mem_range.mp hb) (Finset.mem_range.mp hr) hj).trans_le hPN
  exact ⟨q*H*b+r, by simpa only [mul_zero, add_zero] using hindex 0 hH,
    hindex, hprefix.trans (hmb.trans hmr)⟩

end Hindman168
