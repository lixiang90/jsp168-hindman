import Hindman168.MixedDualConcatenation

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (U : Ultrafilter ℕ) (Q R : ∀ w, AddSubgroup (G w))
  [∀ w, Fintype (Q w)] [∀ w, Fintype (R w)]
  [∀ w, Fintype (Q w ⊔ R w : AddSubgroup (G w))]

/-- Orthogonality to the concatenated sum factor forces the two genuine
factor projections to be orthogonal on the full completed Hilbert space. -/
theorem mixedDualHilbert_pair_projections_orthogonal
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)
    (hz : z ∈ (mixedDualHilbertSubspace p (fun w => Q w ⊔ R w) (d + e - 1) U)ᗮ) :
    inner ℝ ((mixedDualHilbertSubspace p Q d U).starProjection z)
      ((mixedDualHilbertSubspace p R e U).starProjection z) = 0 := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  have hm : V.starProjection (W.starProjection z) ∈ V ⊓ W := by
    constructor
    · exact V.starProjection_apply_mem _
    · exact mixedDualHilbert_projection_preserves_closed_space p R e U hU hs he Q d hd
        (W.starProjection_apply_mem z)
  have hsum := mixedDualHilbert_concatenation p U Q R hU hs d e hd he hm
  rw [Submodule.inner_starProjection_left_eq_right]
  exact (Submodule.mem_orthogonal' _ _).mp hz _ hsum

/-- Actual representatives of the two projections have null weighted
correlation when the test has vanishing concatenated Gowers value. -/
theorem mixedDualHilbert_pair_projections_correlation_tendsto_zero
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (g q r : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hq : hilbertFamilyToCompletion _ U q = (mixedDualHilbertSubspace p Q d U).starProjection
      (hilbertFamilyToCompletion _ U g))
    (hr : hilbertFamilyToCompletion _ U r = (mixedDualHilbertSubspace p R e U).starProjection
      (hilbertFamilyToCompletion _ U g))
    (hzero : Tendsto (fun w => weightedSubgroupGowersValue (Q w ⊔ R w) (p w) (d + e - 1)
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    Tendsto (fun w => ∑ c, p w c * finiteHaarMean
      (fun x => q.val w (c, x) * r.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  have ho := mixedDualHilbert_orthogonal_of_gowers_zero p (fun w => Q w ⊔ R w) (d + e - 1)
    U hs (by omega) g hzero
  have hi := mixedDualHilbert_pair_projections_orthogonal p U Q R hU hs d e hd he
    (hilbertFamilyToCompletion _ U g) ho
  have ht := weightedHaarHilbert_inner_tendsto p U q r
  rwa [hq, hr, hi] at ht

end Hindman168
