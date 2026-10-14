import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Hindman168.NativeLieLowerCentralModel
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Genuine interval integrals remain in a closed original subspace.
The proof uses the actual continuous quotient map and actual integral
commutation. In the original finite-dimensional model, every original
native lower-central layer is genuinely closed, so this applies there. -/

namespace Hindman168
open MeasureTheory Set
open scoped Interval
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

 theorem closedSubmodule_intervalIntegral_mem (S : Submodule ℝ E) (hS : IsClosed (S : Set E))
    {f : ℝ → E} {a b : ℝ} (hf : IntervalIntegrable f volume a b)
    (hmem : ∀ t : ℝ, f t ∈ S) : (∫ t in a..b, f t) ∈ S := by
  letI : IsClosed (S : Set E) := hS
  let q : E →L[ℝ] (E ⧸ S) := ⟨S.mkQ, S.continuous_mkQ⟩
  have hz : ∀ t : ℝ, q (f t) = 0 := by
    intro t
    change (Submodule.Quotient.mk (f t) : E ⧸ S) = 0
    exact (Submodule.Quotient.mk_eq_zero S).mpr (hmem t)
  apply (Submodule.Quotient.mk_eq_zero S).mp
  change q (∫ t in a..b, f t) = 0
  rw [← q.intervalIntegral_comp_comm hf]
  simp only [hz, intervalIntegral.integral_zero]

variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G]
  [LieGroup I ∞ G] [BoundarylessManifold I G] [T2Space G] [FiniteDimensional ℝ E]

attribute [local instance] lieGroup_smooth_min_three

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLowerCentralModel_closed (j : ℕ) :
    IsClosed (nativeLieLowerCentralModel (I := I) (G := G) j : Set E) :=
  (nativeLieLowerCentralModel (I := I) (G := G) j).closed_of_finiteDimensional

omit [BoundarylessManifold I G] [T2Space G] in
 theorem nativeLieLowerCentralModel_intervalIntegral_mem {j : ℕ} {f : ℝ → E} {a b : ℝ}
    (hf : IntervalIntegrable f volume a b)
    (hmem : ∀ t : ℝ, f t ∈ nativeLieLowerCentralModel (I := I) (G := G) j) :
    (∫ t in a..b, f t) ∈ nativeLieLowerCentralModel (I := I) (G := G) j :=
  closedSubmodule_intervalIntegral_mem _ (nativeLieLowerCentralModel_closed j) hf hmem

end Hindman168
