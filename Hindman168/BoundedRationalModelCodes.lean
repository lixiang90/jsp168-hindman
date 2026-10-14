import Mathlib.Data.Int.Interval
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sets
import Mathlib.Data.Fintype.Prod

/-! Finite signatures for bounded rational nilpotent-model data.

This is an independent enumeration lemma, not an inverse theorem and not
yet a construction of nilmanifolds. It records dimension, a covering-lattice
scale, Lie structure constants, and padded filtration-layer coordinates.
Every entry is bounded explicitly. No finiteness premise is assumed.

The covering lattice and the transport of observables must still be proved
when these signatures are connected to actual geometric models.
-/

namespace Hindman168

open scoped Classical

/-- A finite superset of rationals whose reduced numerator and denominator
are bounded by `H`. Zero denominators in the enumeration are harmless. -/
noncomputable def boundedModelRationalCandidates (H : ℕ) : Finset ℚ :=
  ((Finset.Icc (-(H : ℤ)) (H : ℤ)).product (Finset.range (H + 1))).image
    (fun p => (p.1 : ℚ) / (p.2 : ℚ))

theorem mem_boundedModelRationalCandidates {H : ℕ} {q : ℚ}
    (hnum : q.num.natAbs ≤ H) (hden : q.den ≤ H) :
    q ∈ boundedModelRationalCandidates H := by
  apply Finset.mem_image.mpr
  refine ⟨(q.num, q.den), ?_, ?_⟩
  · apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_Icc.mpr
      omega
    · exact Finset.mem_range.mpr (Nat.lt_succ_of_le hden)
  · exact q.num_div_den

/-- Coordinates needed for a rational Lie bracket and padded layer bases. -/
abbrev RationalModelCodeIndex (s d : ℕ) :=
  (Fin d × Fin d × Fin d) ⊕ (Fin (s + 1) × Fin d × Fin d)

/-- Dimension, covering-grid scale, and all rational model coordinates. -/
abbrev RationalModelCode (s : ℕ) :=
  Σ d : ℕ, ℕ × (RationalModelCodeIndex s d → ℚ)

abbrev BoundedRationalModelCode (s D B H : ℕ) :=
  Σ d : Fin (D + 1), Fin (B + 1) ×
    (RationalModelCodeIndex s d.val →
      {q : ℚ // q ∈ boundedModelRationalCandidates H})

def BoundedRationalModelCode.forget {s D B H : ℕ}
    (c : BoundedRationalModelCode s D B H) : RationalModelCode s :=
  ⟨c.1.val, c.2.1.val, fun i => (c.2.2 i).val⟩

/-- One finite list is fixed by the bounds, before any particular model. -/
noncomputable def boundedRationalModelCodes (s D B H : ℕ) :
    Finset (RationalModelCode s) :=
  Finset.univ.image (BoundedRationalModelCode.forget (s := s) (D := D) (B := B) (H := H))

theorem mem_boundedRationalModelCodes {s D B H : ℕ} (c : RationalModelCode s)
    (hdim : c.1 ≤ D) (hgrid : c.2.1 ≤ B)
    (hcoords : ∀ i, (c.2.2 i).num.natAbs ≤ H ∧ (c.2.2 i).den ≤ H) :
    c ∈ boundedRationalModelCodes s D B H := by
  rcases c with ⟨d, grid, coords⟩
  refine Finset.mem_image.mpr ⟨
    ⟨⟨d, Nat.lt_succ_of_le hdim⟩,
      ⟨grid, Nat.lt_succ_of_le hgrid⟩,
      fun i => ⟨coords i,
        mem_boundedModelRationalCandidates (hcoords i).1 (hcoords i).2⟩⟩,
    Finset.mem_univ _, ?_⟩
  rfl

theorem finite_boundedRationalModelCodes (s D B H : ℕ) :
    {c : RationalModelCode s | c.1 ≤ D ∧ c.2.1 ≤ B ∧
      ∀ i, (c.2.2 i).num.natAbs ≤ H ∧ (c.2.2 i).den ≤ H}.Finite := by
  apply (boundedRationalModelCodes s D B H).finite_toSet.subset
  intro c hc
  exact mem_boundedRationalModelCodes c hc.1 hc.2.1 hc.2.2

end Hindman168
