import Hindman168.RoughFiniteFamilyApproximation
import Hindman168.RoughFrozenDiscrepancy

namespace Hindman168
open FiniteMass

theorem rough_finite_family_approximate_discrepancy {ι Y : Type*} [Fintype ι]
    (X : ι → Type*) [∀ j, PseudoMetricSpace (X j)] [∀ j, CompactSpace (X j)]
    [∀ j, Nonempty (X j)] [PseudoMetricSpace Y]
    (φ : (j : ι) → ℝ × X j → Y) (hφ : ∀ j, Continuous (φ j))
    (R B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, ∀ (j : ι) (t : ℝ), |t| ≤ R → ∀ (F : Y → ℝ),
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) →
      ∀ (μ ν : Mass (X j)), (∀ x, 0 ≤ μ x) → (∀ x, 0 ≤ ν x) →
      total μ = 1 → total ν = 1 → ∀ η : ℝ,
      η ≤ |expectation μ (fun x => F (φ j (t, x))) -
        expectation ν (fun x => F (φ j (t, x)))| →
      ∃ g : X j → ℝ, LipschitzWith K g ∧ (∀ x, |g x| ≤ B) ∧
        η - 2 * ε ≤ |expectation μ g - expectation ν g| := by
  obtain ⟨K, hK⟩ := rough_finite_family_lipschitz_approximation X φ hφ R B hB Lip hε
  refine ⟨K, ?_⟩
  intro j t ht F hF hb μ ν hμ hν htμ htν η hbad
  obtain ⟨g, hg, ha, hbound⟩ := hK j t ht F hF hb
  refine ⟨g, hg, hbound, ?_⟩
  exact rough_frozen_discrepancy μ ν hμ hν htμ htν _ g η ε
    (fun x _ => ha x) (fun x _ => ha x) hbad

end Hindman168
