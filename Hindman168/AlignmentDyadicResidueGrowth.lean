import Hindman168.MasterSamplingBudgets

namespace Hindman168
open Filter
open scoped Topology

theorem alignment_exposure_modulus_bound
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F) (w j : ℕ) :
    (F.modulus w : ℕ) * (primorial w) ^ w ≤ F.auxiliary w j ^ 2 := by
  have hm := F.modulus_le_auxiliary w j
  have hp := (Nat.le_of_dvd (F.modulus w).pos (hF.primorial_power_dvd w)).trans hm
  simpa only [pow_two] using Nat.mul_le_mul hm hp

theorem alignment_dyadic_residue_eventually_large
    {n k : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin k) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions n A D F)
    (j : ℕ) (C : ℝ) (hC : 0 < C) :
    ∀ᶠ w in atTop, ∀ x : ℕ, F.cutoff w j ≤ x →
      C * ((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) ≤ (2 ^ Nat.log2 x : ℕ) := by
  have hg := powerDominates_log_to_cutoff (hF.cutoff_auxiliary_growth j)
  have hh := hg.eventually_bound (Eventually.of_forall (fun _ => Nat.cast_nonneg _))
    (Eventually.of_forall (fun _ => Nat.cast_nonneg _)) 2 (by positivity : 0 < 2 * C)
  filter_upwards [hh] with w hw x hx
  have hb : (((F.modulus w : ℕ) * (primorial w) ^ w : ℕ) : ℝ) ≤
      (F.auxiliary w j : ℝ) ^ 2 := by exact_mod_cast alignment_exposure_modulus_bound hF w j
  have hlo : (F.cutoff w j : ℝ) ≤ x := by exact_mod_cast hx
  have hhi : (x : ℝ) < 2 * ((2 ^ Nat.log2 x : ℕ) : ℝ) := by
    have h := Nat.lt_log2_self (n := x)
    rw [pow_succ, mul_comm] at h
    exact_mod_cast h
  nlinarith [mul_le_mul_of_nonneg_left hb hC.le]

end Hindman168
