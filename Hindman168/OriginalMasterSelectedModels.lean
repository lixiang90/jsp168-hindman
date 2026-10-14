import Hindman168.NativeSubprobSelectedModels
import Hindman168.MasterOriginalHilbertLaws

/-! Selected native models for the exact original master pivot masses,
with no normalization premise and no modification of initial stages. -/
namespace Hindman168
open FiniteMass Filter
universe u

noncomputable abbrev originalPivotMass (F : MasterParameterFamily) (i w : ℕ) : Mass ℤ :=
  integerMass (F.cutoff w i) (primorial w)

theorem original_master_selected_models (ι : Type*) [Fintype ι] (n s : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ (M : ℕ) (F : MasterParameterFamily)
      (U : Ultrafilter ℕ)
      (gap : ℕ → ℕ → Fin M),
      (∀ l k, l ≤ k → ∀ w, F.gap w (gap l w).val ∣ F.gap w (gap k w).val) →
      ∀ f : Finset ℕ → (i : ℕ) → ι → boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F i w)),
      (∀ T i a w y, y ∈ (originalPivotMass F i w).support → 0 ≤ (f T i a).val w y ∧ (f T i a).val w y ≤ 1) →
      ∃ e : Fin (2 * n) ↪o ℕ, (∀ j, e j < N) ∧
        ∀ T : Finset ℕ, ∀ b : Fin n, ∀ a : ι,
          ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (originalPivotMass F (energyPrincipal e b) w)),
            NativePieceRepresented.{u} s F (gap (energyPadding e b)) (fun w y => t.val w y) ∧
            (∀ w y, 0 ≤ t.val w y ∧ t.val w y ≤ 1) ∧
            ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                (gap (energyPadding e b))).starProjection
                (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a)) -
              hilbertFamilyToCompletion _ U t‖ < ε ∧
            ∀ v : Fin n, v ≤ b → T ⊆ energyPrincipalSet e →
              (∀ y ∈ T, y < energyPrincipal e v) →
              ‖(nativeNilHilbertSubspace.{u} s F (originalPivotMass F (energyPrincipal e b)) U
                  (gap (energyPadding e v))).starProjection
                  (hilbertFamilyToCompletion _ U (f T (energyPrincipal e b) a) -
                    hilbertFamilyToCompletion _ U t)‖ ≤ 2 * ε := by
  obtain ⟨N, hN⟩ := native_subprob_selected_models.{u} ι n s ε hε
  refine ⟨N, ?_⟩
  intro M F U gap hdiv f hf
  exact hN M F (originalPivotMass F) (fun i w => integerMass_total_le_one _ _) U gap hdiv f hf

end Hindman168
