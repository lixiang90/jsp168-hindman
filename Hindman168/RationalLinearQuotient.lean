import Hindman168.RationalLinearLattice

/-! Compactness and embedded orbits for actual rational linear layers.
These statements are in the natural additive quotient topology. The
nilpotent noncommutative exponential/lattice comparison is not asserted. -/

namespace Hindman168
open Submodule Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A full discrete integer lattice has compact natural additive quotient. -/
theorem integerLattice_quotient_compact [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] :
    CompactSpace (E ⧸ L) := by
  have hc := IsZLattice.isCompact_range_of_periodic L
    (Submodule.Quotient.mk : E → E ⧸ L) continuous_quot_mk (by
      intro z w hw
      apply (Submodule.Quotient.eq L).mpr
      simpa using hw)
  rw [Set.range_eq_univ.mpr (Submodule.Quotient.mk_surjective L)] at hc
  exact isCompact_univ_iff.mp hc

variable [Module ℚ E]

/-- Compactness of the actual restricted quotient is a consequence of
rationality and discreteness, not an input. -/
theorem rationalLinearSubspace_quotient_compact [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (V : Submodule ℝ E) (hV : RationalLinearSubspace L V) :
    CompactSpace (V ⧸ linearLayerLattice L V) := by
  letI := linearLayerLattice_discrete L V
  letI := rationalLinearSubspace_isZLattice L V hV
  exact integerLattice_quotient_compact (linearLayerLattice L V)

omit [Module ℚ E] in
/-- A finite-dimensional real layer is closed independently of rationality. -/
theorem finiteLinearLayer_isClosed [FiniteDimensional ℝ E]
    (V : Submodule ℝ E) : IsClosed (V : Set E) := V.closed_of_finiteDimensional

omit [Module ℚ E] in
/-- The actual inclusion-induced map of integer coset spaces. -/
noncomputable def linearLayerQuotientInclusion (L : Submodule ℤ E) (V : Submodule ℝ E) :
    V ⧸ linearLayerLattice L V → E ⧸ L :=
  Quotient.lift (fun x : V => (Submodule.Quotient.mk x.val : E ⧸ L))
    (fun x y h => by
      apply (Submodule.Quotient.eq' L).mpr
      exact QuotientAddGroup.leftRel_apply.mp h)

omit [Module ℚ E] in
/-- The inclusion map agrees with the actual ambient quotient projection. -/
theorem linearLayerQuotientInclusion_mk (L : Submodule ℤ E) (V : Submodule ℝ E)
    (x : V) : linearLayerQuotientInclusion L V (Submodule.Quotient.mk x) =
    Submodule.Quotient.mk x.val := rfl

omit [Module ℚ E] in
/-- The map uses the natural quotient topology on both sides. -/
theorem linearLayerQuotientInclusion_continuous (L : Submodule ℤ E)
    (V : Submodule ℝ E) : Continuous (linearLayerQuotientInclusion L V) := by
  exact continuous_quot_lift _ (continuous_quot_mk.comp continuous_subtype_val)

omit [Module ℚ E] in
/-- The equivalence relation on the layer is exactly ambient coset equality. -/
theorem linearLayerQuotientInclusion_injective (L : Submodule ℤ E)
    (V : Submodule ℝ E) : Function.Injective (linearLayerQuotientInclusion L V) := by
  intro a b
  induction a, b using Quotient.inductionOn₂ with
  | _ x y =>
    intro h
    apply (Submodule.Quotient.eq (linearLayerLattice L V)).mpr
    exact (Submodule.Quotient.eq L).mp h

/-- The quotient of a rational layer embeds as a closed compact orbit in the
ambient lattice quotient. Ambient cocompactness is unnecessary. -/
theorem rationalLinearSubspace_quotient_closedEmbedding [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (V : Submodule ℝ E) (hV : RationalLinearSubspace L V) :
    IsClosedEmbedding (linearLayerQuotientInclusion L V) := by
  letI := rationalLinearSubspace_quotient_compact L V hV
  letI : IsClosed (L.toAddSubgroup : Set E) := AddSubgroup.isClosed_of_discrete
  exact (linearLayerQuotientInclusion_continuous L V).isClosedEmbedding
    (linearLayerQuotientInclusion_injective L V)

/-- The set of actual projected layer points is compact. -/
theorem rationalLinearSubspace_orbit_isCompact [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L]
    (V : Submodule ℝ E) (hV : RationalLinearSubspace L V) :
    IsCompact ((Submodule.Quotient.mk : E → E ⧸ L) '' (V : Set E)) := by
  letI := linearLayerLattice_discrete L V
  letI := rationalLinearSubspace_isZLattice L V hV
  have hc := IsZLattice.isCompact_range_of_periodic (linearLayerLattice L V)
    (fun x : V => (Submodule.Quotient.mk x.val : E ⧸ L))
    (continuous_quot_mk.comp continuous_subtype_val) (by
      intro z w hw
      apply (Submodule.Quotient.eq L).mpr
      have hw' : w.val ∈ L := hw
      simpa only [Submodule.coe_add, add_sub_cancel_left] using hw')
  have heq : Set.range (fun x : V => (Submodule.Quotient.mk x.val : E ⧸ L)) =
      (Submodule.Quotient.mk : E → E ⧸ L) '' (V : Set E) := by
    ext q
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨x.val, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩
  exact heq ▸ hc

end Hindman168
