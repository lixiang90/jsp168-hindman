import Hindman168.RoughScalarFamilyApproximation

namespace Hindman168

theorem rough_finite_family_lipschitz_approximation {ι Y : Type*} [Fintype ι]
    (X : ι → Type*) [∀ j, PseudoMetricSpace (X j)] [∀ j, CompactSpace (X j)]
    [∀ j, Nonempty (X j)] [PseudoMetricSpace Y]
    (φ : (j : ι) → ℝ × X j → Y) (hφ : ∀ j, Continuous (φ j))
    (R B : ℝ) (hB : 0 ≤ B) (Lip : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : NNReal, ∀ (j : ι) (t : ℝ), |t| ≤ R → ∀ (F : Y → ℝ),
      LipschitzWith Lip F → (∀ y, |F y| ≤ B) →
      ∃ g : X j → ℝ, LipschitzWith K g ∧
        (∀ x, |F (φ j (t, x)) - g x| ≤ ε) ∧ (∀ x, |g x| ≤ B) := by
  classical
  have hh := fun j => rough_scalar_family_lipschitz_approximation (φ j) (hφ j) R B hB Lip hε
  choose K hK using hh
  refine ⟨∑ j, K j, ?_⟩
  intro j t ht F hF hb
  obtain ⟨g, hg, ha, hbound⟩ := hK j t ht F hF hb
  refine ⟨g, hg.weaken ?_, ha, hbound⟩
  exact Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ j)

end Hindman168
