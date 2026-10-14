import Hindman168.SelectedPrincipalScales

/-! Own coarse scales at selected padding indices satisfy the paper's
admissible growth conditions for the selected principal raw coordinates. -/

namespace Hindman168
open Filter
open scoped BigOperators Topology Classical

noncomputable def selectedPrincipalAuxiliary {n : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) : ℕ :=
  2 + (F.modulus w : ℕ) +
    ∏ k ∈ Finset.univ.filter (fun k : Fin n => k < i), F.cutoff w (energyPrincipal e k) ^ 2

theorem MasterParameterConditions.selected_auxiliary_le_padding {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) :
    selectedPrincipalAuxiliary F e w i ≤ F.auxiliary w (energyPadding e i) := by
  let T := (Finset.univ.filter (fun k : Fin n => k < i)).image (energyPrincipal e)
  have hT : T ⊆ Finset.range (energyPadding e i) := by
    intro j hj
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_range.mpr (energyPrincipal_lt_padding e (Finset.mem_filter.mp hk).2)
  have hp : (∏ j ∈ T, F.cutoff w j ^ 2) ≤
      ∏ j ∈ Finset.range (energyPadding e i), F.cutoff w j ^ 2 :=
    Finset.prod_le_prod_of_subset_of_one_le' hT (fun j _ _ =>
      one_le_pow₀ (hF.cutoff_positive w j))
  dsimp only [T] at hp
  rw [Finset.prod_image (energyPrincipal_strictMono e).injective.injOn] at hp
  exact Nat.add_le_add_left hp _

theorem MasterParameterConditions.selected_coarse_growth {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) :
    PowerDominates atTop (fun w => (F.gap w (energyPadding e i) : ℝ))
      (fun w => (selectedPrincipalAuxiliary F e w i : ℝ)) := by
  apply (hF.gap_growth (energyPadding e i)).mono_base 1
  exact Eventually.of_forall (fun w => by
    refine ⟨Nat.cast_nonneg _, by positivity, ?_⟩
    simp only [pow_one]
    have h := hF.selected_auxiliary_le_padding e w i
    exact_mod_cast (show selectedPrincipalAuxiliary F e w i ≤
      (F.pool w (energyPadding e i)).upper + F.auxiliary w (energyPadding e i) from by omega))

theorem MasterParameterConditions.selected_cutoff_coarse_growth {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) :
    PowerDominates atTop (fun w => Real.log (F.cutoff w (energyPrincipal e i) : ℝ))
      (fun w => (F.gap w (energyPadding e i) : ℝ)) := by
  apply (hF.cutoff_growth (energyPrincipal e i)).mono_base 1
  exact Eventually.of_forall (fun w => by
    refine ⟨Nat.cast_nonneg _, Nat.cast_nonneg _, ?_⟩
    simp only [pow_one]
    exact_mod_cast Nat.le_of_dvd (hF.gap_positive w (energyPrincipal e i))
      (hF.gap_earlier_dvd w _ _ (energyPadding_lt_principal e i)))

theorem MasterParameterConditions.selected_coarse_parameters {d n M : ℕ}
    {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) :
    (∀ w i, 0 < F.gap w (energyPadding e i) ∧
      (F.modulus w : ℕ) ∣ F.gap w (energyPadding e i) ∧
      0 < F.cutoff w (energyPrincipal e i) ∧
      ∃ q : ℕ, F.cutoff w (energyPrincipal e i) = 2 ^ q) ∧
    (∀ i, PowerDominates atTop (fun w => (F.gap w (energyPadding e i) : ℝ))
      (fun w => (selectedPrincipalAuxiliary F e w i : ℝ))) ∧
    ∀ i, PowerDominates atTop (fun w => Real.log (F.cutoff w (energyPrincipal e i) : ℝ))
      (fun w => (F.gap w (energyPadding e i) : ℝ)) := by
  refine ⟨?_, hF.selected_coarse_growth e, hF.selected_cutoff_coarse_growth e⟩
  intro w i
  exact ⟨hF.gap_positive w _, hF.gap_modulus_dvd w _,
    hF.cutoff_positive w _, hF.dyadic_cutoff w _⟩

end Hindman168
