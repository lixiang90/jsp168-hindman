import Hindman168.AlternatingEnergyIndices
import Hindman168.RamseyProjectionSelection

/-! The paper's alternating padding/principal selection, with the
tail-cardinality and tuple-validity conditions discharged. -/

namespace Hindman168

theorem alternating_energy_selection (ι : Type*) [Fintype ι] (n : ℕ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ energy : Finset ℕ → ℕ → ℕ → ι → ℝ,
      (∀ T l i a, 0 ≤ energy T l i a ∧ energy T l i a ≤ 1) →
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < N) ∧
        ∀ v u : Fin n, v ≤ u → ∀ T : Finset ℕ,
          T ⊆ energyPrincipalSet e → (∀ t ∈ T, t < energyPrincipal e v) →
          ∀ a, |energy T (energyPadding e v) (energyPrincipal e u) a -
            energy T (energyPadding e u) (energyPrincipal e u) a| < δ := by
  obtain ⟨N, hN⟩ := indexed_energy_selection ι (n + 1) (2 * n) δ hδ
  refine ⟨N, ?_⟩
  intro energy he
  obtain ⟨S, hSN, hSc, hS⟩ := hN energy he
  let e := S.orderEmbOfFin hSc
  have hem : ∀ j, e j ∈ S := fun j => S.orderEmbOfFin_mem hSc j
  refine ⟨e, fun j => Finset.mem_range.mp (hSN (hem j)), ?_⟩
  intro v u hvu T hT hbefore a
  have hTS : T ⊆ S := by
    intro t ht
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp (hT ht)
    exact hem _
  have hcard : T.card + 2 ≤ n + 1 := by
    have := energyTail_card_lt e T v hT hbefore
    omega
  have htv := energyTail_before_padding e T v hT hbefore
  have hvu' := energyPadding_mono e hvu
  exact hS T hTS hcard _ _ _ (hem _) (hem _) (hem _) htv
    (fun t ht => (htv t ht).trans_le hvu')
    (hvu'.trans_lt (energyPadding_lt_principal e u)) (energyPadding_lt_principal e u) a

theorem alternating_projection_selection
    (E : ℕ → Type*) [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
    (ι : Type*) [Fintype ι] (n : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (V : (i : ℕ) → ℕ → Submodule ℝ (E i))
      [∀ i l, (V i l).HasOrthogonalProjection]
      (x : Finset ℕ → (i : ℕ) → ι → E i), (∀ T i a, ‖x T i a‖ ≤ 1) →
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < N) ∧
        ∀ v u : Fin n, v ≤ u → ∀ T : Finset ℕ,
          T ⊆ energyPrincipalSet e → (∀ t ∈ T, t < energyPrincipal e v) →
          ∀ a, |‖(V (energyPrincipal e u) (energyPadding e v)).starProjection
              (x T (energyPrincipal e u) a)‖ ^ 2 -
            ‖(V (energyPrincipal e u) (energyPadding e u)).starProjection
              (x T (energyPrincipal e u) a)‖ ^ 2| < ε ^ 2 := by
  obtain ⟨N, hN⟩ := alternating_energy_selection ι n (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨N, ?_⟩
  intro V inst x hx
  exact hN (fun T l i a => ‖(V i l).starProjection (x T i a)‖ ^ 2)
    (fun T l i a => projection_energy_unit_interval (V i l) (x T i a) (hx T i a))

end Hindman168
