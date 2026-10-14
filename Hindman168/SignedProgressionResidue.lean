import Hindman168.FiniteSequenceFreeze
import Mathlib.Tactic.Ring

/-! Exact residue arithmetic for signed progressions of a fixed period. -/
namespace Hindman168

theorem signed_period_residue_eq_of_modEq (M : ℕ) (hM : 0 < M) {a b : ℤ}
    (hab : Int.ModEq (M : ℤ) a b) : signedPeriodResidue M hM a = signedPeriodResidue M hM b := by
  apply Fin.ext
  change (a % (M : ℤ)).toNat = (b % (M : ℤ)).toNat
  exact congrArg Int.toNat hab

theorem signed_period_residue_progression (M : ℕ) (hM : 0 < M) (b d k : ℤ)
    (hd : (M : ℤ) ∣ d) : signedPeriodResidue M hM (b+d*k) = signedPeriodResidue M hM b := by
  apply signed_period_residue_eq_of_modEq M hM
  apply Int.modEq_iff_dvd.mpr
  obtain ⟨a,ha⟩ := hd
  refine ⟨-(a*k),?_⟩
  rw [ha]
  ring

end Hindman168
