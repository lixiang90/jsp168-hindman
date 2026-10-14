import Hindman168.SelectedPrincipalMicrocellEndpoints
import Hindman168.NormalizedShortBinCutoff
import Hindman168.PositivePrincipalSumHarmonicCellTransfer

/-! Incomplete padding microcells have vanishing mass under the original
principal raw law. The proof keeps the original cutoff and original master
conditions and applies the established normalized endpoint discard. -/
namespace Hindman168
open Filter FiniteMass
open scoped Topology Classical

def selectedAlignmentCompleteCell {n : ℕ} (F : MasterParameterFamily)
    (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) (p : ℕ) : Prop :=
  F.cutoff w (energyPrincipal e i) ≤
    (p / selectedPrincipalMicrocellWidth F e w i) * selectedPrincipalMicrocellWidth F e w i ∧
  (p / selectedPrincipalMicrocellWidth F e w i) * selectedPrincipalMicrocellWidth F e w i +
    selectedPrincipalMicrocellWidth F e w i ≤ F.cutoff w (energyPrincipal e i)^2

/-- The elementary partial-cell event is contained in the already proved
normalized cutoff discard. -/
theorem selected_alignment_partial_cell_failed_cutoff (X R p : ℕ) (hR : 0 < R)
    (hbad : ¬ (X ≤ (p/R)*R ∧ (p/R)*R+R ≤ X^2)) :
    failedCutoffShortBin X R 1 1 p := by
  have hlo : (p/R)*R ≤ p := Nat.div_mul_le_self p R
  have hhi : p < (p/R)*R+R := by
    have hh := Nat.lt_mul_div_succ p hR
    nlinarith
  apply shortBin_bad_endpoints_failed_normalized p
    (Q := ((p/R)*R:ℕ)) (tlo := 1) (t := 1) (C := 1)
    (by norm_num) (by norm_num) (Nat.cast_nonneg _) (by norm_num) (by norm_num)
  · simpa only [one_mul] using (show (((p/R)*R:ℕ):ℝ) ≤ p by exact_mod_cast hlo)
  · simpa only [one_mul, ← Nat.cast_add] using
      (show (p:ℝ) < ((p/R)*R+R:ℕ) by exact_mod_cast hhi)
  · rw [not_and_or, not_le, not_le] at hbad
    rcases hbad with h | h
    · left
      simpa only [one_mul, mul_one] using
        (show (((p/R)*R:ℕ):ℝ) < X by exact_mod_cast h)
    · right
      simpa only [mul_one, one_mul, ← Nat.cast_pow, ← Nat.cast_add] using
        (show ((X^2:ℕ):ℝ) < ((p/R)*R+R:ℕ) by exact_mod_cast h)

theorem selected_alignment_complete_cell_exposure_eq {n : ℕ}
    (F : MasterParameterFamily) (e : Fin (2*n) ↪o ℕ) (w : ℕ) (i : Fin n) (p q : ℕ)
    (hexposure : principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) p =
      principalMicrocellExposure (selectedPrincipalMicrocellWidth F e w i) (F.modulus w) q) :
    selectedAlignmentCompleteCell F e w i p ↔ selectedAlignmentCompleteCell F e w i q := by
  have hd : p / selectedPrincipalMicrocellWidth F e w i =
      q / selectedPrincipalMicrocellWidth F e w i := by
    have hh := congrArg Prod.fst hexposure
    change (p:ℤ) / (selectedPrincipalMicrocellWidth F e w i:ℤ) =
      (q:ℤ) / (selectedPrincipalMicrocellWidth F e w i:ℤ) at hh
    exact_mod_cast hh
  simp only [selectedAlignmentCompleteCell, hd]

theorem selected_alignment_complete_cell_failure_tendsto
    {d n M : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)} {F : MasterParameterFamily}
    (hF : MasterParameterConditions M A D F) (e : Fin (2*n) ↪o ℕ)
    (heM : ∀ j, e j < M) (i : Fin n) :
    Tendsto (fun w => event (rawMass (F.cutoff w (energyPrincipal e i)) (primorial w))
      (fun p => ¬ selectedAlignmentCompleteCell F e w i p)) atTop (𝓝 0) := by
  have hdiscard := selected_principal_microcell_cutoff_discard hF e heM i (fun _ => 1)
    (C := 1) le_rfl (Eventually.of_forall (fun _ => zero_lt_one))
  have hR := (selected_principal_microcell_growth hF e i).1.eventually_bound
    (Eventually.of_forall (fun w => Nat.cast_nonneg (selectedPrincipalMicrocellWidth F e w i)))
    (Eventually.of_forall (fun w => Nat.cast_nonneg (selectedPrincipalAuxiliary F e w i)))
    0 (show (0:ℝ) < 1 by norm_num)
  simp only [pow_zero, mul_one] at hR
  have hnonneg : ∀ᶠ w in atTop, ∀ p,
      0 ≤ rawMass (F.cutoff w (energyPrincipal e i)) (primorial w) p := by
    filter_upwards [hF.raw_cutoffs_valid] with w hw
    intro p
    rw [rawMass_apply]
    exact harmonicWeight_nonneg (hw (energyPrincipal e i)
      (Finset.mem_range.mpr (heM _))).2.2 p
  apply squeeze_zero' _ _ hdiscard
  · exact hnonneg.mono (fun _ hw => event_nonneg _ _ hw)
  · filter_upwards [hnonneg,hR] with w hw hr
    apply event_mono _ hw
    intro p hp
    exact selected_alignment_partial_cell_failed_cutoff _ _ p
      (by exact_mod_cast (lt_of_lt_of_le zero_lt_one hr)) hp

end Hindman168
