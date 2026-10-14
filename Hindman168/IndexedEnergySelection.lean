import Hindman168.EnergyTupleEncoding

/-! Uniform Ramsey selection for the exact (tail, gap, pivot) energy
indices. The bound precedes all energies and the ambient master size. -/

namespace Hindman168

theorem indexed_energy_selection (ι : Type*) [Fintype ι] (K n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ energy : Finset ℕ → ℕ → ℕ → ι → ℝ,
      (∀ T l i a, 0 ≤ energy T l i a ∧ energy T l i a ≤ 1) →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = n ∧
        ∀ T : Finset ℕ, T ⊆ S → T.card + 2 ≤ K →
          ∀ l k i, l ∈ S → k ∈ S → i ∈ S →
            (∀ t ∈ T, t < l) → (∀ t ∈ T, t < k) → l < i → k < i →
            ∀ a, |energy T l i a - energy T k i a| < δ := by
  obtain ⟨N, hN⟩ := finite_energy_homogeneous_bound ι K n δ hδ
  refine ⟨N, ?_⟩
  intro energy he
  let encoded := fun A a => energy (energyTupleTail A) (energyTupleGap A) (energyTuplePivot A) a
  obtain ⟨S, hSN, hSc, hS⟩ := hN encoded (fun A a => he _ _ _ a)
  refine ⟨S, hSN, hSc, ?_⟩
  intro T hTS hK l k i hl hk hi hTl hTk hli hki a
  have h := hS (energyTuple T l i) (energyTuple T k i)
    (energyTuple_subset hTS hl hi) (energyTuple_subset hTS hk hi)
    ((energyTuple_card T l i hTl hli).trans (energyTuple_card T k i hTk hki).symm)
    (by rw [energyTuple_card T l i hTl hli]; exact hK) a
  obtain ⟨hpl, hgl, htl⟩ := energyTuple_decode T l i hTl hli
  obtain ⟨hpk, hgk, htk⟩ := energyTuple_decode T k i hTk hki
  simpa only [encoded, hpl, hgl, htl, hpk, hgk, htk] using h

end Hindman168
