import Hindman168.UniformBoxMassComparison
import Hindman168.UniformIntervalTranslation

namespace Hindman168.FiniteMass
open scoped BigOperators Classical

theorem complexExpectation_push {α β : Type*} (μ : Mass α) (g : α → β) (f : β → ℂ) :
    complexExpectation (μ.mapDomain g) f = complexExpectation μ (fun x => f (g x)) := by
  exact Finsupp.sum_mapDomain_index (by intros; simp)
    (by intros; simp only [Complex.ofReal_add, add_mul])

theorem piMass_translation_complex_bound {ι : Type*} [Fintype ι]
    (μ : ι → Mass ℤ) (u : ι → ℤ) (f : (ι → ℤ) → ℂ) (K : ℝ)
    (hμ : ∀ j z, 0 ≤ μ j z) (ht : ∀ j, total (μ j) = 1)
    (hK : 0 ≤ K) (hf : ∀ z, ‖f z‖ ≤ K) :
    ‖complexExpectation (piMass μ) (fun z => f (fun j => z j + u j)) -
      complexExpectation (piMass μ) f‖ ≤
      K * ∑ j, distance ((μ j).mapDomain (fun z => z + u j)) (μ j) := by
  rw [← complexExpectation_push]
  exact (complexExpectation_difference_bound _ _ f K hf).trans
    (mul_le_mul_of_nonneg_left (piMass_translation_distance μ u hμ ht) hK)

end Hindman168.FiniteMass

