import Hindman168.IndexedEnergySelection
import Hindman168.RamseyProjectionSelection

/-! Pivot-dependent Hilbert spaces: compared tuples retain exactly the
same target vector and the same original pivot law. -/

namespace Hindman168

variable (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]

theorem indexed_projection_selection (ι : Type*) [Fintype ι] (K n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : (i : ℕ) → ℕ → Submodule ℝ (E i))
      [∀ i l, (V i l).HasOrthogonalProjection]
      (x : Finset ℕ → (i : ℕ) → ι → E i),
      (∀ T i a, ‖x T i a‖ ≤ 1) →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = n ∧
        ∀ T : Finset ℕ, T ⊆ S → T.card + 2 ≤ K →
          ∀ l k i, l ∈ S → k ∈ S → i ∈ S →
            (∀ t ∈ T, t < l) → (∀ t ∈ T, t < k) → l < i → k < i →
            ∀ a, |‖(V i l).starProjection (x T i a)‖ ^ 2 -
              ‖(V i k).starProjection (x T i a)‖ ^ 2| < ε ^ 2 := by
  obtain ⟨N, hN⟩ := indexed_energy_selection ι K n (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro V inst x hx
  exact hN (fun T l i a => ‖(V i l).starProjection (x T i a)‖ ^ 2)
    (fun T l i a => projection_energy_unit_interval (V i l) (x T i a) (hx T i a))

theorem indexed_projection_model_selection (ι : Type*) [Fintype ι] (K n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : (i : ℕ) → ℕ → Submodule ℝ (E i))
      [∀ i l, (V i l).HasOrthogonalProjection]
      (x : Finset ℕ → (i : ℕ) → ι → E i),
      (∀ T i a, ‖x T i a‖ ≤ 1) →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = n ∧
        ∀ T : Finset ℕ, T ⊆ S → T.card + 2 ≤ K →
          ∀ l k i, l ∈ S → k ∈ S → i ∈ S →
            (∀ t ∈ T, t < l) → (∀ t ∈ T, t < k) → l < i → k < i →
            ∀ a, V i k ≤ V i l → ∀ t ∈ V i k,
              ‖(V i k).starProjection (x T i a) - t‖ ≤ ε →
              ‖(V i l).starProjection (x T i a - t)‖ ≤ 2 * ε := by
  obtain ⟨N, hN⟩ := indexed_projection_selection E ι K n ε hε
  refine ⟨N, ?_⟩
  intro V inst x hx
  obtain ⟨S, hSN, hSc, hS⟩ := hN V x hx
  refine ⟨S, hSN, hSc, ?_⟩
  intro T hTS hK l k i hl hk hi hTl hTk hli hki a hV t ht he
  have hgap := (le_abs_self _).trans (hS T hTS hK l k i hl hk hi hTl hTk hli hki a).le
  exact nested_projection_model_error _ _ hV _ _ ht hε.le hgap he

end Hindman168
