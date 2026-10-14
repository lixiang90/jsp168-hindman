import Hindman168.OriginalMasterSelectedModels
import Hindman168.MasterGapIndex

/-! Master conditions discharge divisibility for the canonical gap map.
All selected indices are inside the original master range. -/
namespace Hindman168
open FiniteMass Filter
universe u

theorem concrete_master_selected_models (ι : Type*) [Fintype ι] (n s : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (M : ℕ) (hM : 0 < M), N ≤ M →
      ∀ (d : ℕ) (A : Finset ℚ) (D : Finset (MvPolynomial (Fin d) ℤ))
      (F : MasterParameterFamily), MasterParameterConditions M A D F →
      ∀ U : Ultrafilter ℕ,
      ∀ f : Finset ℕ → (i : ℕ) → ι → boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)),
      (∀ T i a w y, y ∈ (originalPivotMass F i w).support → 0 ≤ (f T i a).val w y ∧ (f T i a).val w y ≤ 1) →
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < M) ∧
        (∀ j w, (masterGapIndex M hM (e j) w).val = e j) ∧
        ∀ T : Finset ℕ, ∀ b : Fin n, ∀ a : ι,
          ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F (energyPrincipal e b) w)),
            NativePieceRepresented.{u} s F (masterGapIndex M hM (energyPadding e b)) (fun w y => t.val w y) ∧
            (∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                (masterGapIndex M hM (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U t‖ < ε ∧
            ∀ v : Fin n, v ≤ b → T ⊆ energyPrincipalSet e →
              (∀ y ∈ T, y < energyPrincipal e v) →
              ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                  (masterGapIndex M hM (energyPadding e v))).starProjection
                  (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a) -
                    hilbertFamilyToCompletion _ U t)‖ ≤ 2 * ε := by
  obtain ⟨N, hN⟩ := original_master_selected_models.{u} ι n s ε hε
  refine ⟨N, ?_⟩
  intro M hM hNM d A D F hF U f hf
  obtain ⟨e, heN, he⟩ := hN M F U (masterGapIndex M hM)
    (fun l k hlk w => hF.masterGapIndex_dvd hM l k hlk w) f hf
  have heM : ∀ j, e j < M := fun j => (heN j).trans_le hNM
  exact ⟨e, heM, fun j w => masterGapIndex_val M hM (e j) w (heM j), he⟩

end Hindman168
