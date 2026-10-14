import Hindman168.RationalCoordinateDecomposition

/-! Scalar extension of actual rational coordinate subspaces preserves
intersections in finite coordinate spaces. This is proved by finite rational
components, not by assuming a rational basis or invoking subgroup compactness.
Coordinate-zero slices and arbitrary rational intersections are consequences. -/

noncomputable section
namespace Hindman168
open Set Submodule Module

variable {ι : Type*} [Fintype ι]

 def RationalCoordinateSubspace (V : Submodule ℝ (ι → ℝ)) : Prop :=
  span ℝ ((V : Set (ι → ℝ)) ∩ range (rationalCoordinateCast ι)) = V

 def rationalCoordinatePreimage (V : Submodule ℝ (ι → ℝ)) : Submodule ℚ (ι → ℚ) :=
  (V.restrictScalars ℚ).comap (rationalCoordinateCast ι)

 theorem realSpanRationalCoordinates_inf (U W : Submodule ℚ (ι → ℚ)) :
    realSpanRationalCoordinates (U ⊓ W) =
      realSpanRationalCoordinates U ⊓ realSpanRationalCoordinates W := by
  apply le_antisymm
  · apply span_le.mpr
    rintro x ⟨q, hq, rfl⟩
    exact ⟨subset_span ⟨q, hq.1, rfl⟩, subset_span ⟨q, hq.2, rfl⟩⟩
  · intro x hx
    let b := Basis.ofVectorSpace ℚ ℝ
    have hc : ∀ k, realRationalComponent b k x ∈ U ⊓ W := fun k =>
      ⟨realRationalComponent_mem b k U hx.1, realRationalComponent_mem b k W hx.2⟩
    rw [← realRationalComponent_reconstruct b x]
    apply (realSpanRationalCoordinates (U ⊓ W)).sum_mem
    intro k _
    exact (realSpanRationalCoordinates (U ⊓ W)).smul_mem (b k)
      (subset_span ⟨realRationalComponent b k x, hc k, rfl⟩)

 omit [Fintype ι] in
 theorem realSpanRationalCoordinates_preimage (V : Submodule ℝ (ι → ℝ)) :
    realSpanRationalCoordinates (rationalCoordinatePreimage V) =
      span ℝ ((V : Set (ι → ℝ)) ∩ range (rationalCoordinateCast ι)) := by
  have heq : rationalCoordinateCast ι '' (rationalCoordinatePreimage V : Set (ι → ℚ)) =
      (V : Set (ι → ℝ)) ∩ range (rationalCoordinateCast ι) := by
    ext x
    constructor
    · rintro ⟨q, hq, rfl⟩
      exact ⟨hq, ⟨q, rfl⟩⟩
    · rintro ⟨hx, q, hqx⟩
      refine ⟨q, ?_, hqx⟩
      change rationalCoordinateCast ι q ∈ V
      rw [hqx]
      exact hx
  change span ℝ (rationalCoordinateCast ι '' (rationalCoordinatePreimage V : Set (ι → ℚ))) = _
  rw [heq]

 omit [Fintype ι] in
 theorem rationalCoordinateSubspace_iff_preimage_span (V : Submodule ℝ (ι → ℝ)) :
    RationalCoordinateSubspace V ↔ realSpanRationalCoordinates (rationalCoordinatePreimage V) = V := by
  rw [realSpanRationalCoordinates_preimage]
  rfl

 omit [Fintype ι] in
 theorem rationalCoordinateSubspace_realSpan (U : Submodule ℚ (ι → ℚ)) :
    RationalCoordinateSubspace (realSpanRationalCoordinates U) := by
  apply le_antisymm
  · exact span_le.mpr fun _ hx => hx.1
  · apply span_le.mpr
    rintro x ⟨q, hq, rfl⟩
    exact subset_span ⟨subset_span ⟨q, hq, rfl⟩, ⟨q, rfl⟩⟩

 theorem rationalCoordinateSubspace_inf (V W : Submodule ℝ (ι → ℝ))
    (hV : RationalCoordinateSubspace V) (hW : RationalCoordinateSubspace W) :
    RationalCoordinateSubspace (V ⊓ W) := by
  have hv := (rationalCoordinateSubspace_iff_preimage_span V).mp hV
  have hw := (rationalCoordinateSubspace_iff_preimage_span W).mp hW
  rw [← hv, ← hw, ← realSpanRationalCoordinates_inf]
  exact rationalCoordinateSubspace_realSpan _

 def coordinateZeroSubmodule (R : Type*) [CommRing R] (p : ι → Prop) : Submodule R (ι → R) where
  carrier := {x | ∀ j, p j → x j = 0}
  zero_mem' := by intro j _; rfl
  add_mem' {x y} hx hy := by intro j hj; change x j + y j = 0; rw [hx j hj, hy j hj, add_zero]
  smul_mem' r x hx := by intro j hj; change r * x j = 0; rw [hx j hj, mul_zero]

 theorem realSpanRationalCoordinates_coordinateZero (p : ι → Prop) :
    realSpanRationalCoordinates (coordinateZeroSubmodule ℚ p) = coordinateZeroSubmodule ℝ p := by
  apply le_antisymm
  · apply span_le.mpr
    rintro x ⟨q, hq, rfl⟩ j hj
    change (q j : ℝ) = 0
    rw [hq j hj, Rat.cast_zero]
  · intro x hx
    let b := Basis.ofVectorSpace ℚ ℝ
    have hc : ∀ k, realRationalComponent b k x ∈ coordinateZeroSubmodule ℚ p := by
      intro k j hj
      change b.repr (x j) k = 0
      rw [hx j hj, map_zero, Finsupp.zero_apply]
    rw [← realRationalComponent_reconstruct b x]
    apply (realSpanRationalCoordinates (coordinateZeroSubmodule ℚ p)).sum_mem
    intro k _
    exact (realSpanRationalCoordinates (coordinateZeroSubmodule ℚ p)).smul_mem (b k)
      (subset_span ⟨realRationalComponent b k x, hc k, rfl⟩)

 theorem rationalCoordinateSubspace_coordinateZero (p : ι → Prop) :
    RationalCoordinateSubspace (coordinateZeroSubmodule ℝ p) := by
  rw [← realSpanRationalCoordinates_coordinateZero]
  exact rationalCoordinateSubspace_realSpan _

end Hindman168
