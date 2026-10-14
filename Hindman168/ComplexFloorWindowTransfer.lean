import Hindman168.FiniteComplexSetMean
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! The exact floor-window mean differs from the real-normalized ceil-window
sum by at most 2/L for unit-bounded inputs. Includes the one-point boundary
and the denominator change; no integrality of L is assumed. -/
namespace Hindman168
open Filter
open scoped BigOperators Classical Topology

theorem complex_floor_window_transfer (L : ℝ) (hL : 0 < L) (a : ℤ → ℂ)
    (ha : ∀ z, ‖a z‖ ≤ 1) :
    ‖finiteComplexSetMean (Finset.Ico 0 ⌊L⌋) a - (∑ z ∈ Finset.Ico 0 ⌈L⌉, a z)/(L : ℂ)‖ ≤ 2/L := by
  let S := Finset.Ico (0 : ℤ) ⌊L⌋
  let T := Finset.Ico ⌊L⌋ ⌈L⌉
  have hfloor : (0 : ℤ) ≤ ⌊L⌋ := Int.floor_nonneg.mpr hL.le
  have hsum : (∑ z ∈ Finset.Ico 0 ⌈L⌉, a z) = (∑ z ∈ S, a z)+(∑ z ∈ T, a z) := by
    rw [← Finset.sum_union (show Disjoint S T from by
      apply Finset.disjoint_left.mpr
      intro z hz ht
      exact (not_lt_of_ge (Finset.mem_Ico.mp ht).1) (Finset.mem_Ico.mp hz).2)]
    rw [show S ∪ T = Finset.Ico 0 ⌈L⌉ from
      Finset.Ico_union_Ico_eq_Ico hfloor (Int.floor_le_ceil L)]
  have hcard : (S.card : ℝ) = (⌊L⌋ : ℝ) := by
    have he : (S.card : ℤ) = ⌊L⌋ := by
      simp only [S, Int.card_Ico, sub_zero, Int.toNat_of_nonneg hfloor]
    exact_mod_cast he
  have hTail : T.card ≤ 1 := by
    have he := Int.ceil_le_floor_add_one L
    simp only [T, Int.card_Ico]
    omega
  have hTailNorm : ‖∑ z ∈ T, a z‖ ≤ 1 := by
    have he := finite_complex_sum_norm_bound T a 1 (fun z _ => ha z)
    have hc : (T.card : ℝ) ≤ 1 := by exact_mod_cast hTail
    linarith
  have hMean := finiteComplexSetMean_norm_bound S a 1 zero_le_one (fun z _ => ha z)
  have hden : ‖finiteComplexSetMean S a-(∑ z ∈ S, a z)/(L : ℂ)‖ ≤ 1/L := by
    have he : finiteComplexSetMean S a-(∑ z ∈ S, a z)/(L : ℂ) =
        (((L-(S.card : ℝ))/L : ℝ) : ℂ)*finiteComplexSetMean S a := by
      have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
      rw [← finiteComplexSetMean_mul_card S a]
      push_cast
      field_simp [hLC]
    have hnon : 0 ≤ (L-(S.card : ℝ))/L := by rw [hcard]; exact div_nonneg (sub_nonneg.mpr (Int.floor_le L)) hL.le
    have hratio : (L-(S.card : ℝ))/L ≤ 1/L := by
      apply div_le_div_of_nonneg_right _ hL.le
      rw [hcard]
      linarith [Int.lt_floor_add_one L]
    rw [he, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnon]
    exact (mul_le_mul_of_nonneg_left hMean hnon).trans (by simpa only [mul_one] using hratio)
  have hboundary : ‖(∑ z ∈ S, a z)/(L : ℂ)-(∑ z ∈ Finset.Ico 0 ⌈L⌉, a z)/(L : ℂ)‖ ≤ 1/L := by
    rw [hsum, add_div, sub_add_cancel_left, norm_neg, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    exact div_le_div_of_nonneg_right hTailNorm hL.le
  have ht := dist_triangle (finiteComplexSetMean S a) ((∑ z ∈ S, a z)/(L : ℂ))
    ((∑ z ∈ Finset.Ico 0 ⌈L⌉, a z)/(L : ℂ))
  simp only [dist_eq_norm] at ht
  change ‖finiteComplexSetMean S a-_‖ ≤ 2/L
  rw [show (2 : ℝ)/L = 1/L+1/L by ring]
  exact ht.trans (add_le_add hden hboundary)

theorem complex_floor_window_limit (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (a : ℕ → ℤ → ℂ) (ha : ∀ n z, ‖a n z‖ ≤ 1) (v : ℂ)
    (hv : Tendsto (fun n => (∑ z ∈ Finset.Ico 0 ⌈L n⌉, a n z)/(L n : ℂ)) atTop (𝓝 v)) :
    Tendsto (fun n => finiteComplexSetMean (Finset.Ico 0 ⌊L n⌋) (a n)) atTop (𝓝 v) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have he : 0 < ε/2 := by positivity
  filter_upwards [(Metric.tendsto_nhds.mp hv) (ε/2) he,
    hL.eventually (eventually_gt_atTop (4/ε)),hL.eventually (eventually_gt_atTop 0)] with n hn hLarge hLn
  have hb := complex_floor_window_transfer (L n) hLn (a n) (ha n)
  have hsmall : 2/L n < ε/2 := by
    apply (div_lt_iff₀ hLn).mpr
    have := (div_lt_iff₀ hε).mp hLarge
    nlinarith
  have ht := dist_triangle (finiteComplexSetMean (Finset.Ico 0 ⌊L n⌋) (a n))
    ((∑ z ∈ Finset.Ico 0 ⌈L n⌉, a n z)/(L n : ℂ)) v
  simp only [dist_eq_norm] at hn ht ⊢
  linarith

end Hindman168
