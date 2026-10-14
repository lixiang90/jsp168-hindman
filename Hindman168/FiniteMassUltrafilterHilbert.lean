import Hindman168.FiniteMassL2Space
import Hindman168.UltrafilterHilbertEmbedding

/-! Instantiation of the completed ultrafilter space on the ORIGINAL
sequence of nonnegative finite laws. Its pairing is exactly the ultralimit
of the original weighted expectations. -/

namespace Hindman168
open FiniteMass Filter
open scoped Topology

variable {α : Type*} (μ : ℕ → Mass α) [∀ w, Fact (∀ a, 0 ≤ μ w a)]

noncomputable def finiteMassBoundedFamily (hprob : ∀ w, total (μ w) = 1)
    (f : ℕ → α → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hf : ∀ w a, a ∈ (μ w).support → |f w a| ≤ B) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)) :=
  ⟨f, B, hB, fun w => finiteMassL2_norm_le (μ w) (hprob w) (f w) hB (hf w)⟩

theorem finiteMassHilbert_inner (U : Ultrafilter ℕ)
    (x y : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) :
    inner ℝ (hilbertFamilyToCompletion _ U x) (hilbertFamilyToCompletion _ U y) =
      limUnder (U : Filter ℕ) (fun w => expectation (μ w) (fun a => x.val w a * y.val w a)) := by
  rw [hilbertFamilyToCompletion_inner]
  rfl

theorem finiteMassHilbert_expectation_tendsto (U : Ultrafilter ℕ)
    (x y : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) :
    Tendsto (fun w => expectation (μ w) (fun a => x.val w a * y.val w a)) (U : Filter ℕ)
      (𝓝 (inner ℝ (hilbertFamilyToCompletion _ U x) (hilbertFamilyToCompletion _ U y))) := by
  rw [hilbertFamilyToCompletion_inner]
  exact hilbertFamilyPairing_tendsto _ U x y

theorem finiteMassHilbert_inner_of_tendsto
    (x y : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) (a : ℝ)
    (h : Tendsto (fun w => expectation (μ w) (fun t => x.val w t * y.val w t)) atTop (𝓝 a)) :
    inner ℝ (hilbertFamilyToCompletion _ (hyperfilter ℕ) x)
      (hilbertFamilyToCompletion _ (hyperfilter ℕ) y) = a := by
  rw [hilbertFamilyToCompletion_inner]
  exact hilbertFamilyPairing_hyperfilter_of_tendsto _ x y a h

theorem finiteMassHilbert_eq_iff (U : Ultrafilter ℕ)
    (x y : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w))) :
    hilbertFamilyToCompletion _ U x = hilbertFamilyToCompletion _ U y ↔
      Tendsto (fun w => expectation (μ w) (fun a => (x.val w a - y.val w a) ^ 2))
        (U : Filter ℕ) (𝓝 0) := by
  rw [hilbertFamilyToCompletion_eq_iff]
  simp only [finiteMassL2_norm_sq]
  rfl

end Hindman168
