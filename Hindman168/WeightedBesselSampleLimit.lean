import Hindman168.FiniteWeightedSampleSelection
import Hindman168.WeightedHaarHilbert

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

/-- Sampling from each original weighted index law gives a fixed-size
direction list with uniform empirical mean error and vanishing every
off-diagonal pair statistic on the same tail-containing ultrafilter. -/
theorem weighted_bessel_exists_sample_limit
    {A : ℕ → Type*} (μ : ∀ w, Mass (A w)) (hμ : ∀ w a, 0 ≤ μ w a)
    (ht : ∀ w, total (μ w) = 1)
    (h : ∀ w, A w → ℝ) (hh : ∀ w a, |h w a| ≤ 1)
    (f : ∀ w, A w → A w → ℝ) (hf : ∀ w a b, 0 ≤ f w a b)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (hp : Tendsto (fun w => expectation (μ w)
      (fun a => expectation (μ w) (f w a))) (U : Filter ℕ) (𝓝 0))
    (m : ℕ) (hm : 0 < m) :
    ∃ s : ∀ w, Fin m → A w,
      (∀ w, (finiteHaarMean (fun i => h w (s w i)) - expectation (μ w) (h w)) ^ 2 ≤
        2 / (m : ℝ)) ∧
      ∀ i j, i ≠ j → Tendsto (fun w => f w (s w i) (s w j)) (U : Filter ℕ) (𝓝 0) := by
  have hex (w : ℕ) := expectation_exists_bessel_sample (μ w) (hμ w) (ht w) (h w) (hh w)
    (f w) (hf w) m hm (1 / ((w : ℝ) + 1)) (by positivity)
  choose s hsmean hspair using hex
  refine ⟨s, hsmean, ?_⟩
  let Y := fun w => ∑ i : Fin m, ∑ j : Fin m, if i = j then 0 else f w (s w i) (s w j)
  have hterm (w : ℕ) (i j : Fin m) :
      0 ≤ if i = j then (0 : ℝ) else f w (s w i) (s w j) := by
    split_ifs
    · exact le_rfl
    · exact hf w _ _
  have hYn (w : ℕ) : 0 ≤ Y w :=
    Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hterm w i j))
  have hη : Tendsto (fun w : ℕ => 1 / ((w : ℝ) + 1)) (U : Filter ℕ) (𝓝 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).mono_left hU
  have hupper : Tendsto (fun w => 2 * ((m : ℝ) ^ 2 * expectation (μ w)
      (fun a => expectation (μ w) (f w a)) + 1 / ((w : ℝ) + 1)))
      (U : Filter ℕ) (𝓝 0) := by
    simpa only [mul_zero, add_zero] using ((hp.const_mul ((m : ℝ) ^ 2)).add hη).const_mul 2
  have hY : Tendsto Y (U : Filter ℕ) (𝓝 0) :=
    squeeze_zero' (Eventually.of_forall hYn) (Eventually.of_forall hspair) hupper
  intro i j hij
  have hb (w : ℕ) : f w (s w i) (s w j) ≤ Y w := by
    have hrow := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
      hterm w i k) (Finset.mem_univ j)
    have hall : (∑ l : Fin m, if i = l then 0 else f w (s w i) (s w l)) ≤ Y w :=
      Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
      Finset.sum_nonneg (fun l _ => hterm w k l)) (Finset.mem_univ i)
    have hrow' : f w (s w i) (s w j) ≤
        ∑ l : Fin m, if i = l then 0 else f w (s w i) (s w l) := by
      simpa only [if_neg hij] using hrow
    exact hrow'.trans hall
  exact squeeze_zero' (Eventually.of_forall (fun w => hf w _ _)) (Eventually.of_forall hb) hY

end Hindman168
