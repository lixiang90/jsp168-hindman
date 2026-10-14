import Hindman168.AlignmentRawRetainedScale
import Hindman168.PowerDominationRealRatios
import Hindman168.RoughResidueScaleGrowth
import Hindman168.AlignmentDyadicResidueLimit
import Hindman168.AlignmentTypicalShortPosterior

/-! Genuine paper growth for ACTUAL raw master anchors and retained products.
This discharges the real-power analytic scale hypotheses for arbitrary actual
anchor selectors; actual native polynomial source packets remain separate. -/
namespace Hindman168
open Filter
open scoped Topology

theorem alignment_raw_native_reference_real_ratios
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (hT : ∀ j ∈ T, j < i)
    (d : ℕ) (hd : 0 < d) (K : ℝ) (hK : 0 < K)
    (x : ℕ → Fin n → ℕ) (U : ℕ → Finset (Fin n)) (j : ℕ → Fin n)
    (hvalid : ∀ᶠ w in atTop, x w ∈ (globalRawMass (F.cutoff w) (primorial w) n).support ∧
      U w ⊆ T ∧ j w ∈ T) :
    ∀ a : ℝ, 0 < a → Tendsto (fun w =>
      (alignmentCubeScale F w i T (x w) /
        ((d : ℝ)*alignmentNaturalBlockProduct (x w) (U w)*K)) /
      (((2 ^ Nat.log2 (x w (j w)) : ℕ) : ℝ)^a)) atTop atTop := by
  have hg := alignment_raw_retained_scale_powerDominates hF i T hT d hd x U j hvalid
  have hr := rough_power_domination_real_ratios hg
    (Eventually.of_forall (fun w => by
      have hh : 1 ≤ (2 ^ Nat.log2 (x w (j w)) : ℕ) := Nat.one_le_two_pow
      exact_mod_cast hh))
    (Eventually.of_forall (fun w => by unfold alignmentCubeScale; positivity))
  have hh := rough_residue_scale_paper_ratios hr K hK
  intro a ha
  convert hh a ha using 1
  funext w
  ring

theorem alignment_typical_native_factor_scale_tendsto
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (i : Fin n) (T : Finset (Fin n)) (x : ℕ → Fin n → ℕ) (j : ℕ → T)
    (hvalid : ∀ᶠ w in atTop, alignmentTypicalShortPosterior F w i T (x w)) :
    Tendsto (fun w => ((2 ^ Nat.log2 (x w (j w).val) : ℕ) : ℝ)) atTop atTop := by
  have hpositive : ∀ᶠ w in atTop, 0 < x w (j w).val := by
    filter_upwards [hvalid] with w hw
    by_contra hn
    have hz : x w (j w).val=0 := by omega
    have hg := hw.1 (j w).val (j w).property
    have hcut := hF.cutoff_positive w (j w).val.val
    have hlo := hg.1
    simp only [hz,Nat.log2_zero,pow_zero] at hlo
    have hX : F.cutoff w (j w).val.val=1 := by omega
    have hhi := hg.2
    norm_num [hz,hX] at hhi
  have hratio := alignment_dyadic_residue_ratio_tendsto hF (fun w => (j w).val)
    (fun w => x w (j w).val) (by
      filter_upwards [hvalid,hpositive] with w hw hp
      exact (hw.1 (j w).val (j w).property).1.trans (Nat.log2_self_le hp.ne'))
  apply tendsto_atTop_mono' _ _ hratio
  filter_upwards [] with w
  have hL : (1 : ℝ) ≤ (((F.modulus w : ℕ)*(primorial w)^w : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (F.modulus w).pos
      (Nat.pow_pos (primorial_pos w))).ne'
  exact div_le_self (by positivity) hL

end Hindman168
