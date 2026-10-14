import Hindman168.RoughExactInterpolationModOne
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Tendsto

/-! Failure of escape to infinity gives a genuine bounded subsequence.
Nearest integers supply the EXACT integer/error decomposition and a bounded
scaled real error. The index sequence is strictly increasing, preserving any
cofinal original length sequence. No subsequence or decomposition is an input. -/
namespace Hindman168
open Filter
open scoped Topology

theorem sequential_bounded_subsequence_of_not_atTop (x : ℕ → ℝ)
    (h : ¬ Tendsto x atTop atTop) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, x (f n) ≤ C := by
  have he : ∃ C : ℝ, ¬ ∀ᶠ n in atTop, C ≤ x n := by
    simpa only [tendsto_atTop, not_forall] using h
  obtain ⟨C,hC⟩ := he
  have hf : ∃ᶠ n in atTop, x n < C := by
    change ¬ ∀ᶠ n in atTop, ¬ x n < C
    simpa only [not_lt] using hC
  obtain ⟨f,hf,hbound⟩ := extraction_of_frequently_atTop hf
  exact ⟨max C 1, le_max_right _ _, f, hf,
    fun n => (hbound n).le.trans (le_max_left _ _)⟩

noncomputable def sequentialNearestInteger (x : ℝ) : ℤ := round x

noncomputable def sequentialNearestError (x : ℝ) : ℝ := x - (sequentialNearestInteger x : ℝ)

theorem sequential_nearest_decomposition (x : ℝ) :
    x = (sequentialNearestInteger x : ℝ) + sequentialNearestError x := by
  dsimp only [sequentialNearestError]
  ring

theorem sequential_nearest_error_norm (x : ℝ) :
    |sequentialNearestError x| = ‖(x : UnitAddCircle)‖ := UnitAddCircle.norm_eq.symm

theorem sequential_circle_failure_decomposition (L x : ℕ → ℝ)
    (hL : Tendsto L atTop atTop) (hpos : ∀ n, 0 < L n) (j : ℕ)
    (h : ¬ Tendsto (fun n => (L n)^j * ‖(x n : UnitAddCircle)‖) atTop atTop) :
    ∃ C : ℝ, 1 ≤ C ∧ ∃ f : ℕ → ℕ, StrictMono f ∧ Tendsto (L ∘ f) atTop atTop ∧
      ∀ n, x (f n) = (sequentialNearestInteger (x (f n)) : ℝ) + sequentialNearestError (x (f n)) ∧
        (L (f n))^j * |sequentialNearestError (x (f n))| ≤ C ∧
        |sequentialNearestError (x (f n))| ≤ C * (L (f n))⁻¹^j := by
  obtain ⟨C,hC,f,hf,hbound⟩ := sequential_bounded_subsequence_of_not_atTop _ h
  refine ⟨C,hC,f,hf,hL.comp hf.tendsto_atTop, ?_⟩
  intro n
  have hs : (L (f n))^j * |sequentialNearestError (x (f n))| ≤ C := by
    rw [sequential_nearest_error_norm]
    exact hbound n
  refine ⟨sequential_nearest_decomposition _, hs, ?_⟩
  have he : |sequentialNearestError (x (f n))| ≤ C / (L (f n))^j := by
    apply (le_div_iff₀ (pow_pos (hpos (f n)) j)).mpr
    simpa only [mul_comm] using hs
  simpa only [div_eq_mul_inv, inv_pow] using he

end Hindman168
