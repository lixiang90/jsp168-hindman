import Hindman168.MaskTargetAffineRoot
import Hindman168.MasterAffineSamplingGrowth

/-! The actual target monomial multiplier fits inside every original pivot
cutoff once the gap precedes the pivots. Polynomial caps are computed from
the concrete coefficient; arithmetic validity is not an additional premise. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter Asymptotics
open scoped Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (C : ℕ → Chain (m + 1))
  (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetRootMultiplierExponent : ℕ :=
  let P := (maskGeneratedRowDataFamily m gap t).rows.row
    (maskGeneratedRowDataFamily m gap t).target (targetRootAnchor gap t)
  integerPolynomialCoeffSize P + P.totalDegree

noncomputable def targetRootMultiplierCap (w : ℕ) : ℕ :=
  (((maskGeneratedMaster m gap).pool w (gap w).val).upper +
    (maskGeneratedMaster m gap).auxiliary w (gap w).val) ^ targetRootMultiplierExponent gap t

theorem targetRootMultiplier_le_cap (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) :
    targetRootMultiplier gap t x ≤ targetRootMultiplierCap gap t w := by
  apply integerPolynomial_eval_fixed_power_cap
  · have hv := (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
    omega
  · intro j
    have hp := (primePool_mem.mp (primeIndependentMass_support_pool hx.1 j)).2.1
    omega

include hC in
theorem targetRootMultiplier_sampling_log_growth
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) (col : Fin (m + 1)) :
    PowerDominates atTop (fun w => Real.log ((maskGeneratedMaster m gap).cutoff w ((C w).pivot col) : ℝ))
      (fun w => (samplingSize (primorial w) (targetRootMultiplierCap gap t w) 0
        ((maskGeneratedMaster m gap).auxiliary w (gap w).val) : ℝ)) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  let pivot : ℕ → Fin N := fun w =>
    ⟨(C w).pivot col, Finset.mem_range.mp (hC w col (by simp [Chain.block]))⟩
  exact hF.earlier_pool_power_affine_log_growth gap pivot (targetRootMultiplierExponent gap t)
    (hgap.mono (fun w hw => hw col))

include hC in
theorem targetRootMultiplier_eventually_le_cutoff
    (hgap : ∀ᶠ w in atTop, ∀ col, (gap w).val ≤ (C w).pivot col) :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ col,
      targetRootMultiplier gap t x ≤ (maskGeneratedMaster m gap).cutoff w ((C w).pivot col) := by
  have hg := eventually_all.mpr (fun col => sampling_eventually_geometry
    (powerDominates_log_to_cutoff (targetRootMultiplier_sampling_log_growth gap C hC t hgap col)))
  filter_upwards [hg] with w hw
  intro x hx col
  exact (targetRootMultiplier_le_cap gap t w x hx).trans (hw col).2.2

end Hindman168.MaskOriginalSampling
