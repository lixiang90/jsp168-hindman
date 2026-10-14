import Hindman168.NativeOriginalCommonBadFamily
import Hindman168.NativeOriginalActualHorizontalKernelDescent
import Hindman168.RoughNativeZeroDimension

/-! The strengthened rough comparison target is a proposition, not an
axiom. Every raw source/box/observable is quantified AFTER the fixed length
and asymptotic threshold. Its genuine dimension-zero base is proved. -/
namespace Hindman168
open Filter
open scoped Manifold ContDiff
universe u

def NativeNoLongBadFamilyStatement {s : ℕ} (D : NativeNilmanifoldData.{u} s) : Prop :=
  ∀ (n d : ℕ) (c C B η : ℝ) (L : NNReal),
    0 < c → 1 ≤ C → 0 ≤ B → 0 < η →
    ∀ (Scale Z : ℕ → ℝ), Tendsto Scale atTop atTop →
    (∀ a : ℝ, 0 < a → Tendsto (fun w => Z w/(Scale w)^a) atTop atTop) →
    ∃ H : ℕ, 0 < H ∧ ∀ᶠ w in atTop,
      ¬ RoughNativeBadFamily (κ := Fin n) D H w (Scale w) (Z w) d c C L B η

theorem native_no_long_bad_family_zero {s : ℕ} (D : NativeNilmanifoldData.{u} s)
    (hDim : Module.finrank ℝ D.E=0) : NativeNoLongBadFamilyStatement D := by
  intro n d c C B η L _hc _hC _hB hη Scale Z _hScale _hr
  exact ⟨1,by omega,Filter.Eventually.of_forall (fun w =>
    rough_native_zero_dimension_no_bad_family D hDim 1 w (Scale w) (Z w) d c C L B η (by omega) hη)⟩

end Hindman168
