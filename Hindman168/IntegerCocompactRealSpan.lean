import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Instances.Real.Lemmas

/-! Actual compactness of an additive integer-submodule quotient forces
its full real span. A proper real span supplies a nonzero real linear
functional; its genuine continuous quotient map would surject onto R,
contradicting compactness. Discreteness then gives a full Z-lattice. -/

namespace Hindman168
open Function Set Submodule

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

 theorem integerSubmodule_real_span_top_of_compact_quotient (L : Submodule ℤ E)
    [CompactSpace (E ⧸ L)] : span ℝ (L : Set E) = ⊤ := by
  by_contra hspan
  obtain ⟨f, hf, hker⟩ := (span ℝ (L : Set E)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  have hL : L ≤ (f.restrictScalars ℤ).ker := fun x hx => hker (subset_span hx)
  let q : (E ⧸ L) →ₗ[ℤ] ℝ := L.liftQ (f.restrictScalars ℤ) hL
  have hcont : Continuous q := continuous_quot_lift _ f.continuous_of_finiteDimensional
  obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hf
  have hv' : f v ≠ 0 := by simpa only [LinearMap.zero_apply] using hv
  have hsurj : Surjective q := by
    intro r
    refine ⟨Submodule.Quotient.mk ((r / f v) • v), ?_⟩
    change f ((r / f v) • v) = r
    rw [map_smul]
    exact div_mul_cancel₀ r hv'
  have hc := isCompact_range hcont
  rw [range_eq_univ.mpr hsurj] at hc
  exact noncompact_univ ℝ hc

 theorem integerSubmodule_isZLattice_of_compact_quotient (L : Submodule ℤ E)
    [DiscreteTopology L] [CompactSpace (E ⧸ L)] : IsZLattice ℝ L :=
  ⟨integerSubmodule_real_span_top_of_compact_quotient L⟩

end Hindman168
