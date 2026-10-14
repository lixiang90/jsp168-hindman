import Hindman168.NativeNoLongBadFamilyInductionStep

/-! UNCONDITIONAL strengthened original native rough comparison: true
strong NATURAL finrank induction discharges all smaller-native premises. -/
namespace Hindman168
open scoped Manifold ContDiff
universe u

theorem native_no_long_bad_family {s : ℕ} (D : NativeNilmanifoldData.{u} s) :
    NativeNoLongBadFamilyStatement D := by
  have hAll : ∀ r : ℕ, ∀ D0 : NativeNilmanifoldData.{u} s,
      Module.finrank ℝ D0.E=r → NativeNoLongBadFamilyStatement D0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      intro D0 hRank
      by_cases h0 : r=0
      · exact native_no_long_bad_family_zero D0 (by simpa only [h0] using hRank)
      exact native_no_long_bad_family_induction_step D0 (fun D1 hLess =>
        ih (Module.finrank ℝ D1.E) (by simpa only [hRank] using hLess) D1 rfl)
  exact hAll (Module.finrank ℝ D.E) D rfl

end Hindman168
