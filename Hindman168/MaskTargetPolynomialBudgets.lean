import Hindman168.PolynomialAffineSizeBounds
import Hindman168.HarmonicSupportedCoordinates

/-! Concrete polynomial budgets for the actual generated target row and
translation modulus, using original supported primes and master coefficients. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def rootPoolBudget (w : ℕ) : ℕ :=
  ((maskGeneratedMaster m gap).pool w (gap w).val).upper +
    (maskGeneratedMaster m gap).auxiliary w (gap w).val

noncomputable def targetRootRowExponent : ℕ :=
  (maskGeneratedRowDataFamily m gap t).rows.rowValueSizeExponent (maskGeneratedRowDataFamily m gap t).target

noncomputable def targetRootDenExponent : ℕ :=
  integerPolynomialCoeffSize ((maskGeneratedRowDataFamily m gap t).rows.denominator
    (maskGeneratedRowDataFamily m gap t).target) +
    ((maskGeneratedRowDataFamily m gap t).rows.denominator (maskGeneratedRowDataFamily m gap t).target).totalDegree

theorem rootPoolBudget_ge_two (w : ℕ) : 2 ≤ rootPoolBudget (m := m) gap w := by
  have h := (maskGeneratedMaster m gap).auxiliary_ge_two w (gap w).val
  unfold rootPoolBudget
  omega

theorem rootPoolBudget_supported_primes (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) (j : Fin (maskGeneratedRowDataFamily m gap t).arity) :
    x j ≤ rootPoolBudget (m := m) gap w := by
  have h := (primePool_mem.mp (primeIndependentMass_support_pool hx.1 j)).2.1
  unfold rootPoolBudget
  omega

include ha hC in
theorem actualColumnBounds_eventually :
    ∀ᶠ w in atTop, ∀ col,
      0 < masterColumnCoefficient N a (fun w => (C w).block) w col ∧
      masterColumnCoefficient N a (fun w => (C w).block) w col ∣ ((maskGeneratedMaster m gap).modulus w : ℕ) ∧
      masterColumnCoefficient N a (fun w => (C w).block) w col ≤
        (maskGeneratedMaster m gap).auxiliary w (gap w).val := by
  have hA : ∀ q ∈ Finset.univ.image a, 0 < q := by
    intro q hq
    obtain ⟨col, _, rfl⟩ := Finset.mem_image.mp hq
    exact ha col
  have hF := maskGeneratedMaster_conditions m gap (Finset.univ.image a) hA
  filter_upwards [hF.column_coefficients_bounds a
    (fun col => Finset.mem_image.mpr ⟨col, Finset.mem_univ _, rfl⟩)
    (fun w => (C w).block) hC (fun w col => (C w).block_nonempty col)] with w hw
  intro col
  exact ⟨(hw col).1, (hw col).2.1,
    (hw col).2.2.trans ((maskGeneratedMaster m gap).modulus_le_auxiliary w (gap w).val)⟩

include ha hC in
theorem targetRootCoefficient_bound_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ col,
      ((maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskGeneratedRowDataFamily m gap t).target col).natAbs ≤
          (maskGeneratedMaster m gap).auxiliary w (gap w).val *
            rootPoolBudget (m := m) gap w ^ targetRootRowExponent gap t := by
  filter_upwards [actualColumnBounds_eventually (m := m) gap a ha C hC] with w hc
  intro x hx col
  exact (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow_size_bound x
    (masterColumnCoefficient N a (fun w => (C w).block) w) _ col
    (rootPoolBudget_ge_two gap w) (rootPoolBudget_supported_primes gap t w x hx) (hc col).2.2

theorem targetRootTranslationModulus_bound (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (hx : maskGeneratedCopiedPrimeGood m gap t w x) :
    (maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
      (maskGeneratedRowDataFamily m gap t).target ≤
        (maskGeneratedMaster m gap).auxiliary w (gap w).val *
          rootPoolBudget (m := m) gap w ^ targetRootDenExponent gap t :=
  (maskGeneratedRowDataFamily m gap t).rows.translationModulus_size_bound _ w x _
    (rootPoolBudget_ge_two gap w) (rootPoolBudget_supported_primes gap t w x hx)
    ((maskGeneratedMaster m gap).modulus_le_auxiliary w (gap w).val)

theorem targetRootMultiplierExponent_le_rowExponent :
    targetRootMultiplierExponent gap t ≤ targetRootRowExponent gap t :=
  (maskGeneratedRowDataFamily m gap t).rows.rowValueSizeExponent_entry_le _ (targetRootAnchor gap t)

end Hindman168.MaskOriginalSampling
