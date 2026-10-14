import Hindman168.NativeStageRestriction
import Hindman168.SubprobabilityHilbertBounds

/-! Restriction to an ultrafilter-large stage set preserves the actual
completed vector and retains the native representation. -/
namespace Hindman168
open FiniteMass Filter
open scoped Classical Topology
universe u

variable (μ : ℕ → Mass ℤ) [∀ w, Fact (∀ y, 0 ≤ μ w y)]

noncomputable def subprobabilityStageRestrict (hprob : ∀ w, total (μ w) ≤ 1)
    (v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1) (A : Set ℕ) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)) :=
  subprobabilityBoundedFamily μ hprob (fun w y => if w ∈ A then v.val w y else 0)
    1 zero_le_one (fun w y hy => by split_ifs; exact hb w y hy; norm_num)

theorem subprobabilityStageRestrict_eq (U : Ultrafilter ℕ)
    (hprob : ∀ w, total (μ w) ≤ 1)
    (v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1)
    (A : Set ℕ) (hA : A ∈ U) :
    hilbertFamilyToCompletion _ U (subprobabilityStageRestrict μ hprob v hb A) =
      hilbertFamilyToCompletion _ U v := by
  apply (hilbertFamilyToCompletion_eq_iff _ U _ v).mpr
  have he : (fun w => ‖(subprobabilityStageRestrict μ hprob v hb A).val w - v.val w‖ ^ 2)
      =ᶠ[U] fun _ => (0 : ℝ) := by
    filter_upwards [hA] with w hw
    have hv : (subprobabilityStageRestrict μ hprob v hb A).val w = v.val w := by
      funext y
      exact if_pos hw
    rw [hv, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)]
  exact (tendsto_congr' he).mpr tendsto_const_nhds

theorem nativeStageRestrict_represented {s N : ℕ} (F : MasterParameterFamily)
    (gap : ℕ → Fin N) (hprob : ∀ w, total (μ w) ≤ 1)
    (v : boundedHilbertFamilies (fun w => FiniteMassL2 (μ w)))
    (hb : ∀ w y, y ∈ (μ w).support → |v.val w y| ≤ 1)
    (hv : NativePieceRepresented.{u} s F gap (fun w y => v.val w y)) (A : Set ℕ) :
    NativePieceRepresented.{u} s F gap
      (fun w y => (subprobabilityStageRestrict μ hprob v hb A).val w y) :=
  nativePieceRepresented_stage_restrict F gap _ hv A

end Hindman168
