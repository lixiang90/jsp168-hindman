import Hindman168.RationalCoordinateIntersection

/-! Taking the real span of an actual rational coordinate subspace
does not create new rational vectors. An actual Hamel component of 1
with nonzero rational coefficient recovers the original rational vector,
without assuming a rational intersection theorem. -/

namespace Hindman168
open Set Submodule Module

variable {ι : Type*}

 theorem rationalCoordinateCast_mem_realSpan_iff
    (U : Submodule ℚ (ι → ℚ)) (q : ι → ℚ) :
    rationalCoordinateCast ι q ∈ realSpanRationalCoordinates U ↔ q ∈ U := by
  constructor
  · intro hq
    let b := Basis.ofVectorSpace ℚ ℝ
    have hex : ∃ k, b.repr (1 : ℝ) k ≠ 0 := by
      by_contra hn
      push Not at hn
      have he : b.repr (1 : ℝ) = 0 := Finsupp.ext hn
      exact one_ne_zero (b.repr.injective (he.trans b.repr.map_zero.symm))
    obtain ⟨k, hk⟩ := hex
    have hm := realRationalComponent_mem b k U hq
    have he : realRationalComponent b k (rationalCoordinateCast ι q) =
        (b.repr (1 : ℝ) k) • q := by
      simpa only [one_smul] using realRationalComponent_smul_cast b k (1 : ℝ) q
    rw [he] at hm
    exact (smul_mem_iff U hk).mp hm
  · intro hq
    exact subset_span ⟨q, hq, rfl⟩

 theorem rationalCoordinatePreimage_realSpan_eq
    (U : Submodule ℚ (ι → ℚ)) :
    rationalCoordinatePreimage (realSpanRationalCoordinates U) = U := by
  ext q
  exact rationalCoordinateCast_mem_realSpan_iff U q

end Hindman168
