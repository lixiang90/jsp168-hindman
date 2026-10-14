import Mathlib.Algebra.Module.ZLattice.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.RingTheory.Finiteness.Defs

/-! A finite spanning family of integer periods gives a compact range.
The standard integer lattice is used only in the finite real parameter
space; the target's topology and any nonnormal homogeneous space are kept
unchanged. No norm or lattice identification is needed on the target. -/

namespace Hindman168
open Set Submodule Topology

variable {E F : Type*} [AddCommGroup E] [Module ℝ E]
  [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [TopologicalSpace F]

 theorem finite_integer_periods_compact_range {ι : Type*} [Fintype ι]
    (L : Submodule ℤ E) (v : ι → E) (hv : ∀ i, v i ∈ L)
    (hspan : span ℝ (range v) = ⊤)
    (f : E → F) (hf : Continuous f)
    (hper : ∀ x w, w ∈ L → f (x + w) = f x) : IsCompact (range f) := by
  classical
  let Φ : (ι → ℝ) →ₗ[ℝ] E := Fintype.linearCombination ℝ v
  have hΦ : Continuous Φ := by
    change Continuous (fun t : ι → ℝ => ∑ i, t i • v i)
    exact continuous_finsetSum _ fun i _ => (continuous_apply i).smul continuous_const
  have hsurj : Function.Surjective Φ := by
    apply LinearMap.range_eq_top.mp
    rw [Fintype.range_linearCombination]
    exact hspan
  let L0 : Submodule ℤ (ι → ℝ) := span ℤ (range (Pi.basisFun ℝ ι))
  letI : DiscreteTopology L0 := inferInstanceAs
    (DiscreteTopology (span ℤ (range (Pi.basisFun ℝ ι))))
  letI : IsZLattice ℝ L0 := inferInstanceAs
    (IsZLattice ℝ (span ℤ (range (Pi.basisFun ℝ ι))))
  have hmap : L0 ≤ L.comap (Φ.restrictScalars ℤ) := by
    apply span_le.mpr
    rintro x ⟨i, rfl⟩
    change Fintype.linearCombination ℝ v ((Pi.basisFun ℝ ι) i) ∈ L
    simpa only [Pi.basisFun_apply, Fintype.linearCombination_apply_single, one_smul] using hv i
  have hc := IsZLattice.isCompact_range_of_periodic L0 (f ∘ Φ) (hf.comp hΦ) (by
    intro x w hw
    change f (Φ (x + w)) = f (Φ x)
    rw [map_add]
    exact hper _ _ (hmap hw))
  have hr : range (f ∘ Φ) = range f := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨Φ x, rfl⟩
    · rintro ⟨z, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj z
      exact ⟨x, rfl⟩
  exact hr ▸ hc

 theorem spanning_integer_periods_compact_range [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) (hspan : span ℝ (L : Set E) = ⊤)
    (f : E → F) (hf : Continuous f)
    (hper : ∀ x w, w ∈ L → f (x + w) = f x) : IsCompact (range f) := by
  classical
  have hfg : (span ℝ (L : Set E)).FG := by
    rw [hspan]
    exact Module.Finite.fg_top
  obtain ⟨s, hsub, hs⟩ := (fg_span_iff_fg_span_finset_subset (L : Set E)).mp hfg
  let v : s → E := Subtype.val
  have hr : range v = (s : Set E) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩; exact y.property
    · intro hx; exact ⟨⟨x, hx⟩, rfl⟩
  apply finite_integer_periods_compact_range L v (fun i => hsub i.property) _ f hf hper
  rw [hr]
  exact hs.symm.trans hspan

end Hindman168
