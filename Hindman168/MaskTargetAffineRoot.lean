import Hindman168.MaskTargetCubeRootLaw
import Hindman168.PolynomialAffineRootSplit
import Hindman168.AffineRootErrorRates
import Hindman168.AffineProgressionAverage

/-! Actual target anchor, positive monomial multiplier and primorial offset.
These arithmetic certificates use the original supported pool tuple and
master chain. They do not postulate an affine-root comparison. -/

set_option maxHeartbeats 2000000

namespace Hindman168.MaskOriginalSampling

open Filter
open scoped BigOperators Topology Classical
open FiniteMass

variable {m N : ℕ} (gap : ℕ → Fin N) (a : Fin (m + 1) → ℚ) (ha : ∀ col, 0 < a col)
  (C : ℕ → Chain (m + 1)) (hC : ∀ w col, (C w).block col ⊆ Finset.range N)
  (t : Fin (Fintype.card (LargeColumnSubset m)))

noncomputable def targetRootAnchor : Fin (m + 1) :=
  (maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor (maskGeneratedRowDataFamily m gap t).target

noncomputable def targetRootMultiplier
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ) : ℕ :=
  (MvPolynomial.eval (fun j => (x j : ℤ)) ((maskGeneratedRowDataFamily m gap t).rows.row
    (maskGeneratedRowDataFamily m gap t).target (targetRootAnchor gap t))).natAbs

noncomputable def targetRootOffset (w : ℕ)
    (x : Fin (maskGeneratedRowDataFamily m gap t).arity → ℕ)
    (rest : {col : Fin (m + 1) // col ≠ targetRootAnchor gap t} → ℤ)
    (v : MaskOriginalDirection m gap t → ℤ × ℤ) : ℤ :=
  (maskGeneratedRowDataFamily m gap t).rows.normalizedRootOffset x
    (masterColumnCoefficient N a (fun w => (C w).block) w)
    (maskGeneratedRowDataFamily m gap t).target rest +
    ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
      (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, (v k).1

include ha hC in
theorem targetRoot_arithmetic_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x →
      0 < targetRootMultiplier gap t x ∧ (primorial w).Coprime (targetRootMultiplier gap t x) ∧
      (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
        (masterColumnCoefficient N a (fun w => (C w).block) w)
        (maskGeneratedRowDataFamily m gap t).target (targetRootAnchor gap t) =
          (targetRootMultiplier gap t x : ℤ) := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskGenerated_chain_integer_row_conditions m gap a ha C hC,
    maskGenerated_rows_eventually_bounded_units m gap, hF.primorial_le_modulus] with w hr hu hW
  intro x hx
  let F := (maskGeneratedRowDataFamily m gap t).rows
  let i := (maskGeneratedRowDataFamily m gap t).target
  have hn : F.row i (F.normalizationAnchor i) ≠ 0 := F.normalizationAnchor_ne_zero i
  have hm := (maskGeneratedRowDataFamily_monomial m gap t i).monomial_of_ne_zero _ hn
  have hp := (maskGenerated_rows_prime_arithmetic m gap t w x hx.1 hx.2 i).1 _ hn
  have hc := (hu t x hx.1 i _ hn (primorial w) (primorial_pos w)
    (hW.trans ((maskGeneratedMaster m gap).modulus_le_auxiliary w (gap w).val))).1.symm
  refine ⟨hp, hc, ?_⟩
  exact ((hr t x).anchor i).trans (hm.eval_eq_natAbs x)

include ha hC in
theorem cubeRootValue_affine_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ rest v y,
      cubeRootValue gap a C t w x (insertPivotCoordinate (targetRootAnchor gap t) rest y) v =
        (targetRootMultiplier gap t x : ℤ) * y + targetRootOffset gap a C t w x rest v := by
  filter_upwards [targetRoot_arithmetic_eventually gap a ha C hC t] with w hw
  intro x hx rest v y
  unfold cubeRootValue targetRootOffset
  have hp := (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerLinearForm_pivot x
    (masterColumnCoefficient N a (fun w => (C w).block) w)
    (maskGeneratedRowDataFamily m gap t).target rest y
  have hc : (maskGeneratedRowDataFamily m gap t).rows.normalizedIntegerRow x
      (masterColumnCoefficient N a (fun w => (C w).block) w)
      (maskGeneratedRowDataFamily m gap t).target
      ((maskGeneratedRowDataFamily m gap t).rows.normalizationAnchor
        (maskGeneratedRowDataFamily m gap t).target) = (targetRootMultiplier gap t x : ℤ) :=
    (hw x hx).2.2
  rw [hc] at hp
  exact (congrArg (fun q : ℤ => q +
    ((maskGeneratedRowDataFamily m gap t).rows.translationModulus (maskGeneratedMaster m gap) w x
      (maskGeneratedRowDataFamily m gap t).target : ℤ) * ∑ k, (v k).1) hp).trans (by ring)

include ha hC in
theorem targetRootOffset_W_eventually :
    ∀ᶠ w in atTop, ∀ x, maskGeneratedCopiedPrimeGood m gap t w x → ∀ rest v,
      (primorial w : ℤ) ∣ targetRootOffset gap a C t w x rest v := by
  have hF := maskGeneratedMaster_conditions m gap (∅ : Finset ℚ) (by simp)
  filter_upwards [maskGenerated_chain_integer_row_conditions m gap a ha C hC,
    hF.primorial_dvd_modulus] with w hr hW
  intro x _ rest v
  unfold targetRootOffset
  apply dvd_add ((hr t x).rootOffset_W _ rest)
  apply dvd_mul_of_dvd_left
  apply Int.natCast_dvd_natCast.mpr
  exact hW.trans (dvd_mul_right _ _)

end Hindman168.MaskOriginalSampling
