import Hindman168.PositivePrincipalSumPivotBoundary
import Hindman168.MasterDivisorSampling

namespace Hindman168
open Filter
open scoped Topology

/-- Every fixed polynomial displacement allowed by the finite plan has
vanishing harmonic translation loss under the original master conditions. -/
theorem principal_master_harmonic_boundary_tendsto
    {d N : ℕ} {A : Finset ℚ} {D : Finset (MvPolynomial (Fin d) ℤ)}
    {F : MasterParameterFamily} (hF : MasterParameterConditions N A D F)
    (i p : ℕ) (C : ℝ) (hC : 0 ≤ C) :
    Tendsto (fun w => 2 * (C * (F.auxiliary w i : ℝ) ^ p) /
      ((F.cutoff w i : ℝ) * (Real.log (F.cutoff w i : ℝ) -
        (primorial w : ℝ) / F.cutoff w i))) atTop (𝓝 0) := by
  have hg := powerDominates_log_to_cutoff (hF.cutoff_auxiliary_growth i)
  have haux : Tendsto (fun w => (F.auxiliary w i : ℝ) / F.cutoff w i) atTop (𝓝 0) := by
    simpa using (hg 1).tendsto_div_nhds_zero
  have hw : Tendsto (fun w => (primorial w : ℝ) / F.cutoff w i) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => by positivity)) _ haux
    filter_upwards [hF.primorial_le_modulus] with w hw
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    exact_mod_cast hw.trans (F.modulus_le_auxiliary w i)
  apply principal_harmonic_boundary_tendsto atTop _ _ _
    (tendsto_natCast_atTop_atTop.comp (hF.cutoff_tendsto i)) hw
  · simpa [mul_div_assoc] using ((hg p).tendsto_div_nhds_zero.const_mul C)
  · exact Eventually.of_forall (fun _ => mul_nonneg hC (pow_nonneg (Nat.cast_nonneg _) _))
end Hindman168
