import Hindman168.SelectedAdmissibleParameters
import Hindman168.MasterMicrocellGrowth
import Hindman168.AlignedSqrtBoundaryRates

/-! Selected alignment uses the model's PADDING gap and the PRINCIPAL raw
cutoff. No master scale is replaced and no recipe is refined backwards. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology

noncomputable def selectedPrincipalMicrocellWidth {n : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) : ℕ :=
  alignedSqrtMicrocellWidth (F.gap w (energyPadding e i)) (F.modulus w)

noncomputable def selectedPrincipalMicrocellLength {n : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) : ℕ :=
  Nat.sqrt (F.gap w (energyPadding e i)) / (F.modulus w : ℕ)

theorem selected_principal_microcell_exact {n : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) :
    (F.modulus w : ℕ) * selectedPrincipalMicrocellLength F e w i =
      selectedPrincipalMicrocellWidth F e w i := rfl

theorem selected_principal_microcell_growth
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) :
    PowerDominates atTop (fun w => (selectedPrincipalMicrocellWidth F e w i : ℝ))
      (fun w => (selectedPrincipalAuxiliary F e w i : ℝ)) ∧
    PowerDominates atTop (fun w => (selectedPrincipalMicrocellLength F e w i : ℝ))
      (fun w => (selectedPrincipalAuxiliary F e w i : ℝ)) := by
  have hQ : ∀ᶠ w in atTop, (2 : ℝ) ≤ selectedPrincipalAuxiliary F e w i :=
    Eventually.of_forall (fun w => by
      exact_mod_cast (show 2 ≤ selectedPrincipalAuxiliary F e w i by
        unfold selectedPrincipalAuxiliary; omega))
  have hM : ∀ᶠ w in atTop, 0 < (F.modulus w : ℕ) ∧
      (F.modulus w : ℝ) ≤ (selectedPrincipalAuxiliary F e w i : ℝ)^1 := by
    apply Eventually.of_forall
    intro w
    refine ⟨(F.modulus w).pos, ?_⟩
    rw [pow_one]
    exact_mod_cast (show (F.modulus w : ℕ) ≤ selectedPrincipalAuxiliary F e w i by
      unfold selectedPrincipalAuxiliary; omega)
  exact ⟨alignedSqrtMicrocellWidth_growth _ _ _ (hF.selected_coarse_growth e i) 1 hQ hM,
    alignedSqrtMicrocellLength_growth _ _ _ (hF.selected_coarse_growth e i) 1 hQ hM⟩

theorem selected_principal_microcell_length_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) :
    Tendsto (fun w => (selectedPrincipalMicrocellLength F e w i : ℝ)) atTop atTop := by
  apply tendsto_atTop.2
  intro C
  have hh := (selected_principal_microcell_growth hF e i).2.eventually_bound
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) 0
    (show 0 < max C 1 by positivity)
  simp only [pow_zero, mul_one] at hh
  exact hh.mono (fun _ h => (le_max_left C 1).trans h)

theorem selected_principal_microcell_cutoff_ratio
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) :
    Tendsto (fun w => (selectedPrincipalMicrocellWidth F e w i : ℝ) /
      F.cutoff w (energyPrincipal e i)) atTop (𝓝 0) := by
  have hh := ((powerDominates_log_to_cutoff (hF.selected_cutoff_coarse_growth e i)) 1).tendsto_div_nhds_zero
  simp only [pow_one] at hh
  apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ hh
  exact Eventually.of_forall (fun w => div_le_div_of_nonneg_right
    (by exact_mod_cast alignedSqrtWidth_le (F.gap w (energyPadding e i)) (F.modulus w))
    (Nat.cast_nonneg _))

theorem selected_principal_microcell_displacement_ratio
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) (p : ℕ) (C : ℝ) :
    Tendsto (fun w => C * (selectedPrincipalAuxiliary F e w i : ℝ)^p /
      selectedPrincipalMicrocellWidth F e w i) atTop (𝓝 0) := by
  simpa only [mul_div_assoc, mul_zero] using
    (((selected_principal_microcell_growth hF e i).1 p).tendsto_div_nhds_zero).const_mul C

theorem selected_principal_microcell_model_boundary_ratio
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ) (i : Fin n) (p : ℕ) (C : ℝ) :
    Tendsto (fun w => C * (selectedPrincipalAuxiliary F e w i : ℝ)^p *
      selectedPrincipalMicrocellWidth F e w i / F.gap w (energyPadding e i)) atTop (𝓝 0) := by
  have hk : Tendsto (fun w => ((selectedPrincipalAuxiliary F e w i ^ p : ℕ) : ℝ)^2 /
      F.gap w (energyPadding e i)) atTop (𝓝 0) := by
    simpa only [Nat.cast_pow, ← pow_mul] using
      ((hF.selected_coarse_growth e i) (p*2)).tendsto_div_nhds_zero
  have hh := nat_sqrt_margin_ratio_tendsto
    (fun w => selectedPrincipalAuxiliary F e w i ^ p)
    (fun w => selectedPrincipalMicrocellWidth F e w i)
    (fun w => F.gap w (energyPadding e i))
    (Eventually.of_forall (fun w => hF.gap_positive w _))
    (Eventually.of_forall (fun w => Nat.mul_div_le _ _)) hk
  simpa only [Nat.cast_pow, mul_div_assoc, mul_zero, mul_assoc] using hh.const_mul C
end Hindman168
