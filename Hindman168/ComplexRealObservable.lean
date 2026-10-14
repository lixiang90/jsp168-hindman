import Hindman168.FiniteComplexRealComponents

namespace Hindman168

theorem complex_lipschitz_real_part {β : Type*} [PseudoMetricSpace β]
    {L : NNReal} {F : β → ℂ} (hF : LipschitzWith L F) :
    LipschitzWith L (fun x => (F x).re) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (F x).re (F y).re = |(F x-F y).re| := by rw [Real.dist_eq, Complex.sub_re]
    _ ≤ ‖F x-F y‖ := Complex.abs_re_le_norm _
    _ ≤ (L : ℝ)*dist x y := by simpa only [dist_eq_norm] using hF.dist_le_mul x y

theorem complex_lipschitz_imaginary_part {β : Type*} [PseudoMetricSpace β]
    {L : NNReal} {F : β → ℂ} (hF : LipschitzWith L F) :
    LipschitzWith L (fun x => (F x).im) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  calc
    dist (F x).im (F y).im = |(F x-F y).im| := by rw [Real.dist_eq, Complex.sub_im]
    _ ≤ ‖F x-F y‖ := Complex.abs_im_le_norm _
    _ ≤ (L : ℝ)*dist x y := by simpa only [dist_eq_norm] using hF.dist_le_mul x y

/-- The selected component may vary with the observable and sampling laws.
No extra coloring is required when the tests already vary with the index. -/
theorem complex_discrepancy_real_observable {α β : Type*} [PseudoMetricSpace β]
    (μ ν : FiniteMass.Mass α) (Q : α → β) (F : β → ℂ) (L : NNReal) (B : ℝ)
    (hL : LipschitzWith L F) (hB : ∀ x, ‖F x‖ ≤ B) :
    ∃ G : β → ℝ, LipschitzWith L G ∧ (∀ x, |G x| ≤ B) ∧
      ‖FiniteMass.complexExpectation μ (fun x => F (Q x))-
        FiniteMass.complexExpectation ν (fun x => F (Q x))‖/2 ≤
      |FiniteMass.expectation μ (fun x => G (Q x))-
        FiniteMass.expectation ν (fun x => G (Q x))| := by
  rcases FiniteMass.complex_discrepancy_component μ ν (fun x => F (Q x)) with hr | hi
  · exact ⟨fun x => (F x).re, complex_lipschitz_real_part hL,
      fun x => (Complex.abs_re_le_norm (F x)).trans (hB x), hr⟩
  · exact ⟨fun x => (F x).im, complex_lipschitz_imaginary_part hL,
      fun x => (Complex.abs_im_le_norm (F x)).trans (hB x), hi⟩

end Hindman168
