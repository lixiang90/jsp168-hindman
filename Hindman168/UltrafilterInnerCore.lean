import Hindman168.BoundedHilbertFamilies

/-! The actual ultralimit pairing is positive semidefinite and bilinear.
No positive definiteness is assumed before taking the zero-norm quotient. -/

namespace Hindman168
open Filter
open scoped Topology

variable (E : ℕ → Type*) [∀ w, SeminormedAddCommGroup (E w)]
  [∀ w, InnerProductSpace ℝ (E w)] (U : Ultrafilter ℕ)

theorem hilbertFamilyPairing_comm (x y : boundedHilbertFamilies E) :
    hilbertFamilyPairing E U x y = hilbertFamilyPairing E U y x := by
  unfold hilbertFamilyPairing
  congr 1
  funext w
  exact real_inner_comm _ _

theorem hilbertFamilyPairing_nonneg (x : boundedHilbertFamilies E) :
    0 ≤ hilbertFamilyPairing E U x x :=
  ge_of_tendsto (hilbertFamilyPairing_tendsto E U x x)
    (Eventually.of_forall (fun _ => real_inner_self_nonneg))

theorem hilbertFamilyPairing_add_left (x y z : boundedHilbertFamilies E) :
    hilbertFamilyPairing E U (x + y) z =
      hilbertFamilyPairing E U x z + hilbertFamilyPairing E U y z := by
  apply tendsto_nhds_unique (hilbertFamilyPairing_tendsto E U (x + y) z)
  simpa only [Submodule.coe_add, Pi.add_apply, inner_add_left] using
    (hilbertFamilyPairing_tendsto E U x z).add (hilbertFamilyPairing_tendsto E U y z)

theorem hilbertFamilyPairing_smul_left (x y : boundedHilbertFamilies E) (r : ℝ) :
    hilbertFamilyPairing E U (r • x) y = r * hilbertFamilyPairing E U x y := by
  apply tendsto_nhds_unique (hilbertFamilyPairing_tendsto E U (r • x) y)
  simpa only [Submodule.coe_smul, Pi.smul_apply, real_inner_smul_left] using
    (hilbertFamilyPairing_tendsto E U x y).const_mul r

@[implicit_reducible]
noncomputable def ultrafilterInnerCore : PreInnerProductSpace.Core ℝ (boundedHilbertFamilies E) where
  inner := hilbertFamilyPairing E U
  conj_inner_symm x y := hilbertFamilyPairing_comm E U y x
  re_inner_nonneg := hilbertFamilyPairing_nonneg E U
  add_left := hilbertFamilyPairing_add_left E U
  smul_left := hilbertFamilyPairing_smul_left E U

end Hindman168
