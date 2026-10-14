import Hindman168.NestedProjectionEnergy
import Hindman168.RamseyEnergySelection

/-! The uniform finite gap-energy selection and its fine-projection estimate.
All labels are selected together. Actual nilsequence spaces and their
representatives must still instantiate the explicit Hilbert-space data. -/

namespace Hindman168

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem projection_energy_unit_interval (U : Submodule ℝ E) [U.HasOrthogonalProjection]
    (x : E) (hx : ‖x‖ ≤ 1) : 0 ≤ ‖U.starProjection x‖ ^ 2 ∧ ‖U.starProjection x‖ ^ 2 ≤ 1 := by
  have h := (U.norm_starProjection_apply_le x).trans hx
  exact ⟨sq_nonneg _, by nlinarith [norm_nonneg (U.starProjection x)]⟩

theorem finite_projection_gap_selection (ι : Type*) [Fintype ι] (K n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Finset ℕ → ι → Submodule ℝ E)
      [∀ A a, (V A a).HasOrthogonalProjection] (x : Finset ℕ → ι → E),
      (∀ A a, ‖x A a‖ ≤ 1) →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = n ∧
        ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → A.card = B.card → A.card ≤ K →
          ∀ a, |‖(V A a).starProjection (x A a)‖ ^ 2 -
            ‖(V B a).starProjection (x B a)‖ ^ 2| < ε ^ 2 := by
  obtain ⟨N, hN⟩ := finite_energy_homogeneous_bound ι K n (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro V inst x hx
  exact hN (fun A a => ‖(V A a).starProjection (x A a)‖ ^ 2)
    (fun A a => projection_energy_unit_interval (V A a) (x A a) (hx A a))

theorem finite_projection_model_selection (ι : Type*) [Fintype ι] (K n : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : Finset ℕ → ι → Submodule ℝ E)
      [∀ A a, (V A a).HasOrthogonalProjection] (x : Finset ℕ → ι → E),
      (∀ A a, ‖x A a‖ ≤ 1) →
      ∃ S : Finset ℕ, S ⊆ Finset.range N ∧ S.card = n ∧
        ∀ A B : Finset ℕ, A ⊆ S → B ⊆ S → A.card = B.card → A.card ≤ K →
          ∀ a, V B a ≤ V A a → x B a = x A a →
            ∀ s ∈ V B a, ‖(V B a).starProjection (x B a) - s‖ ≤ ε →
              ‖(V A a).starProjection (x A a - s)‖ ≤ 2 * ε := by
  obtain ⟨N, hN⟩ := finite_projection_gap_selection (E := E) ι K n ε hε
  refine ⟨N, ?_⟩
  intro V inst x hx
  obtain ⟨S, hSN, hSc, hS⟩ := hN V x hx
  refine ⟨S, hSN, hSc, ?_⟩
  intro A B hAS hBS hcard hK a hV hxeq s hs happrox
  have hgap := (le_abs_self _).trans (hS A B hAS hBS hcard hK a).le
  rw [hxeq] at hgap happrox
  exact nested_projection_model_error (V B a) (V A a) hV (x A a) s hs hε.le hgap happrox

end Hindman168
