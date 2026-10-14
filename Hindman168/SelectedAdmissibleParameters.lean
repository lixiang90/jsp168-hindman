import Hindman168.SelectedPrincipalGrowth

/-! The selected principal coordinates, their individual master scales
and own padding gaps form the admissible parameter family of the paper.
The original independent harmonic mass is retained literally. -/

namespace Hindman168
open Filter FiniteMass
open scoped BigOperators Topology Classical

structure SelectedAdmissibleFamily {n : ℕ} (M : ℕ) (e : Fin (2*n) ↪o ℕ)
    (F : MasterParameterFamily) : Prop where
  modulus_smooth : ∀ w, ∃ q : ℕ, (F.modulus w : ℕ) = (primorial w) ^ q
  modulus_power : ∀ w, (primorial w) ^ w ∣ (F.modulus w : ℕ)
  subset_scales : ∀ w S, 0 < selectedSubsetScale M e w S ∧
    (∃ q : ℕ, selectedSubsetScale M e w S = (primorial w) ^ q) ∧
    selectedSubsetScale M e w S ≤ (F.modulus w : ℕ) ∧
    (S.Nonempty → (primorial w) ^ w ∣ selectedSubsetScale M e w S)
  adding_scales : ∀ w P T j i, P.Nonempty → T.Nonempty →
    (∀ p ∈ P, ∀ t ∈ T, p < t) → (∀ t ∈ T, t < j) → j < i →
    selectedSubsetScale M e w (insert i T) * (primorial w) ^ w ∣
      selectedSubsetScale M e w (insert j P)
  coarse_positive : ∀ w i, 0 < F.gap w (energyPadding e i)
  coarse_modulus : ∀ w i, (F.modulus w : ℕ) ∣ F.gap w (energyPadding e i)
  cutoff_positive : ∀ w i, 0 < F.cutoff w (energyPrincipal e i)
  cutoff_dyadic : ∀ w i, ∃ q : ℕ, F.cutoff w (energyPrincipal e i) = 2 ^ q
  coarse_growth : ∀ i, PowerDominates atTop (fun w => (F.gap w (energyPadding e i) : ℝ))
    (fun w => (selectedPrincipalAuxiliary F e w i : ℝ))
  cutoff_growth : ∀ i, PowerDominates atTop
    (fun w => Real.log (F.cutoff w (energyPrincipal e i) : ℝ))
    (fun w => (F.gap w (energyPadding e i) : ℝ))
  raw_probability : ∀ᶠ w in atTop, (∀ x, 0 ≤ selectedPrincipalRawMass e F w x) ∧
    total (selectedPrincipalRawMass e F w) = 1

theorem MasterParameterConditions.selected_admissible_family {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) : SelectedAdmissibleFamily M e F := by
  refine {
    modulus_smooth := hF.smooth_modulus
    modulus_power := hF.primorial_power_dvd
    subset_scales := ?_
    adding_scales := hF.selected_adding_scales e heM
    coarse_positive := fun w i => hF.gap_positive w _
    coarse_modulus := fun w i => hF.gap_modulus_dvd w _
    cutoff_positive := fun w i => hF.cutoff_positive w _
    cutoff_dyadic := fun w i => hF.dyadic_cutoff w _
    coarse_growth := hF.selected_coarse_growth e
    cutoff_growth := hF.selected_cutoff_coarse_growth e
    raw_probability := hF.selected_principal_raw_probability e heM }
  intro w S
  refine ⟨selectedSubsetScale_positive e heM w S, ?_,
    (hF.selected_subset_scale_bound e heM w S).2, selectedSubsetScale_power_dvd e heM w S⟩
  rw [selectedSubsetScale_eq_master e heM]
  exact ⟨_, rfl⟩

end Hindman168
