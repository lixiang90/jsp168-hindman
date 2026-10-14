import Hindman168.SelectedPrincipalMicrocellGrowth

namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical

/-- Original principal raw law with the genuinely finer padding microcell.
The old cutoff-discard theorem permits any width below the principal gap;
only the correct one-way divisibility padding→principal is used. -/
theorem selected_principal_microcell_cutoff_discard
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) (tlo : ℕ → ℝ) {C : ℝ} (hC : 1 ≤ C)
    (htlo : ∀ᶠ w in atTop, 0 < tlo w) :
    Tendsto (fun w => event (rawMass (F.cutoff w (energyPrincipal e i)) (primorial w))
      (failedCutoffShortBin (F.cutoff w (energyPrincipal e i))
        (selectedPrincipalMicrocellWidth F e w i) (tlo w) C)) atTop (𝓝 0) := by
  apply master_failedCutoffShortBin_tendsto hF (fun _ => selectedPrincipalIndex e heM i)
    _ tlo hC _ htlo
  apply Eventually.of_forall
  intro w
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have hgap : F.gap w (energyPadding e i) ≤ F.gap w (energyPrincipal e i) :=
    Nat.le_of_dvd (hF.gap_positive w _) (hF.gap_earlier_dvd w _ _ (energyPadding_lt_principal e i))
  exact_mod_cast (alignedSqrtWidth_le (F.gap w (energyPadding e i)) (F.modulus w)).trans hgap
end Hindman168
