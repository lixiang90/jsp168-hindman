import Hindman168.MixedDualGowersModel
import Hindman168.UltrafilterBoundedDiagonal

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- Countable diagonalization realizes the actual projection by one unit-interval
family when the ultrafilter contains every tail of the stage sequence. -/
theorem mixedDualHilbert_projection_exact_representative
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t =
        (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) := by
  have ha (n : ℕ) := mixedDualHilbert_projection_unit_approximation p Q d U hs hd f hf
    (show 0 < 1 / ((n : ℝ) + 1) by positivity)
  choose a hb _ he using ha
  have hnorm : ∀ n w, ‖(a n).val w‖ ≤ 1 := by
    intro n w
    apply finiteMassL2_norm_le _ (weightedHaarMass_total (p w) (hs w)) _ zero_le_one
    intro z _
    rw [abs_of_nonneg (hb n w z.1 z.2).1]
    exact (hb n w z.1 z.2).2
  obtain ⟨t, _, ht, htimage⟩ := ultrafilterHilbert_bounded_diagonal _ U hU
    (fun w t => ∀ c x, 0 ≤ t (c, x) ∧ t (c, x) ≤ 1)
    ((mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f))
    a 1 zero_le_one hnorm (fun n w => hb n w) he
  exact ⟨t, ht, htimage⟩

/-- One actual unit-interval model represents the projection exactly, and the
remaining weighted Gowers value converges to zero along the same tail-containing ultrafilter. -/
theorem mixedDualHilbert_exact_model
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t =
        (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) ∧
      Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
        (fun c x => f.val w (c, x) - t.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  obtain ⟨t, ht, he⟩ := mixedDualHilbert_projection_exact_representative p Q d U hU hs hd f hf
  have hg : ∀ w c x, |(f - t).val w (c, x)| ≤ 1 := by
    intro w c x
    change |f.val w (c, x) - t.val w (c, x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hf w c x).1, (ht w c x).2],
      by linarith [(hf w c x).2, (ht w c x).1]⟩
  have ho : hilbertFamilyToCompletion _ U (f - t) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
    have hm : hilbertFamilyToCompletion _ U (f - t) =
        hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t :=
      (hilbertFamilyCompletionLinearMap _ U).map_sub f t
    rw [hm, he]
    exact (mixedDualHilbertSubspace p Q d U).sub_starProjection_mem_orthogonal _
  exact ⟨t, ht, he, mixedDualHilbert_gowers_zero_of_orthogonal p Q d U hs hd (f - t) hg ho⟩

end Hindman168
