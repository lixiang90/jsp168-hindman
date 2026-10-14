import Hindman168.UltrafilterInnerCore
import Mathlib.Analysis.InnerProductSpace.Completion

/-! The separated completion of the actual ultralimit seminorm.
Completion identifies zero-distance families; its canonical map preserves
the ultralimit pairing and has dense range. -/

namespace Hindman168
open Filter UniformSpace
open scoped Topology

variable (E : ℕ → Type*) [∀ w, SeminormedAddCommGroup (E w)]
  [∀ w, InnerProductSpace ℝ (E w)] (U : Ultrafilter ℕ)

-- A type synonym prevents the coordinatewise product topology from
-- being selected instead of the intended ultralimit seminorm topology.
def UltrafilterFamily (E : ℕ → Type*) [∀ w, SeminormedAddCommGroup (E w)]
    [∀ w, InnerProductSpace ℝ (E w)] (_U : Ultrafilter ℕ) : Type _ := boundedHilbertFamilies E

instance ultrafilterFamilyAddGroup : AddCommGroup (UltrafilterFamily E U) :=
  inferInstanceAs (AddCommGroup (boundedHilbertFamilies E))

instance ultrafilterFamilyModule : Module ℝ (UltrafilterFamily E U) :=
  inferInstanceAs (Module ℝ (boundedHilbertFamilies E))

noncomputable instance ultrafilterFamilySeminormedGroup : SeminormedAddCommGroup (UltrafilterFamily E U) :=
  letI : PreInnerProductSpace.Core ℝ (UltrafilterFamily E U) := ultrafilterInnerCore E U
  InnerProductSpace.Core.toSeminormedAddCommGroup (𝕜 := ℝ)

noncomputable instance ultrafilterFamilyInnerProduct : InnerProductSpace ℝ (UltrafilterFamily E U) :=
  InnerProductSpace.ofCore (show PreInnerProductSpace.Core ℝ (UltrafilterFamily E U) from
    ultrafilterInnerCore E U)

def UltrafilterHilbertSpace : Type _ := Completion (UltrafilterFamily E U)

noncomputable instance ultrafilterHilbertNormedGroup : NormedAddCommGroup (UltrafilterHilbertSpace E U) := by
  change NormedAddCommGroup (Completion (UltrafilterFamily E U))
  infer_instance

noncomputable instance ultrafilterHilbertInnerProduct : InnerProductSpace ℝ (UltrafilterHilbertSpace E U) := by
  change InnerProductSpace ℝ (Completion (UltrafilterFamily E U))
  infer_instance

instance ultrafilterHilbertComplete : CompleteSpace (UltrafilterHilbertSpace E U) := by
  change CompleteSpace (Completion (UltrafilterFamily E U))
  infer_instance

noncomputable def hilbertFamilyToCompletion (x : boundedHilbertFamilies E) : UltrafilterHilbertSpace E U :=
  ((show UltrafilterFamily E U from x) : Completion (UltrafilterFamily E U))

theorem hilbertFamilyToCompletion_inner (x y : boundedHilbertFamilies E) :
    inner ℝ (hilbertFamilyToCompletion E U x) (hilbertFamilyToCompletion E U y) =
      hilbertFamilyPairing E U x y := by
  exact Completion.inner_coe (show UltrafilterFamily E U from x) (show UltrafilterFamily E U from y)

theorem hilbertFamilyToCompletion_dense : DenseRange (hilbertFamilyToCompletion E U) := by
  exact Completion.denseRange_coe (α := UltrafilterFamily E U)

end Hindman168
