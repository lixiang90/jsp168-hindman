import Hindman168.WeightedHaarMultiplication
import Hindman168.MixedDualExactModel

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (u : ∀ w, κ w → G w → ℝ) (hu : ∀ w c x, |u w c x| ≤ 1)
  (hull : ∀ w c, u w c ∈ subgroupMixedDualHull (Q w) d)

include hull

theorem mixedDualHilbert_multiplier_generator
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c, (fun x => f.val w (c, x)) ∈ subgroupMixedDualHull (Q w) d) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f) ∈ mixedDualHilbertGenerators p Q d U := by
  exact ⟨weightedHaarMultiplier p u hu f,
    fun w c => subgroupMixedDualHull_mul_mem (Q w) d (hull w c) (hf w c), rfl⟩

theorem mixedDualHilbert_multiplier_scaled_span (hs : ∀ w, ∑ c, p w c = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (B : ℝ) (hf : ∀ w c, ∃ v ∈ subgroupMixedDualHull (Q w) d,
      (fun x => f.val w (c, x)) = B • v) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f) ∈
      Submodule.span ℝ (mixedDualHilbertGenerators p Q d U) := by
  choose v hv he using hf
  have hp (w : ℕ) (c : κ w) : (fun x => u w c x * v w c x) ∈ subgroupMixedDualHull (Q w) d :=
    subgroupMixedDualHull_mul_mem (Q w) d (hull w c) (hv w c)
  let a := weightedHaarBoundedFamily p hs (fun w c x => u w c x * v w c x) 1 zero_le_one
    (fun w c x => subgroupMixedDualHull_abs_le_one (Q w) d (hp w c) x)
  have hrep : weightedHaarMultiplier p u hu f = B • a := by
    apply Subtype.ext
    funext w
    funext z
    change u w z.1 z.2 * f.val w z = B * (u w z.1 z.2 * v w z.1 z.2)
    have hx : f.val w z = B * v w z.1 z.2 := congrFun (he w z.1) z.2
    rw [hx]
    ring
  rw [hrep]
  change (hilbertFamilyCompletionLinearMap _ U) (B • a) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ B (Submodule.subset_span ⟨a, hp, rfl⟩)

theorem mixedDualHilbert_multiplier_closed (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertSubspace p Q d U) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f) ∈ mixedDualHilbertSubspace p Q d U := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨B, _, t, _, ht, _, he⟩ := mixedDualHilbert_closed_approximation p Q d U hd hf hε
  refine ⟨hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu t),
    mixedDualHilbert_multiplier_scaled_span p Q d U u hu hull hs t B ht, ?_⟩
  rw [dist_eq_norm]
  exact (weightedHaarMultiplier_hilbert_distance_le p U u hu f t).trans_lt he

theorem mixedDualHilbert_multiplier_orthogonal
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu g) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
  rw [mixedDualHilbertSubspace, Submodule.orthogonal_closure, Submodule.mem_orthogonal']
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    rw [weightedHaarMultiplier_hilbert_inner]
    exact (Submodule.mem_orthogonal' _ _).mp hg _ (Submodule.le_topologicalClosure _
      (Submodule.subset_span (mixedDualHilbert_multiplier_generator p Q d U u hu hull f hf)))
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]

/-- Pull out an actual unit mixed-dual-hull multiplier from the genuine projection,
using any actual representative of the projected input. -/
theorem mixedDualHilbert_projection_pullout (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (ht : hilbertFamilyToCompletion _ U t =
      (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f)) :
    (mixedDualHilbertSubspace p Q d U).starProjection
        (hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f)) =
      hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu t) := by
  have hm : hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U := by
    rw [ht]
    exact Submodule.starProjection_apply_mem _ _
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (mixedDualHilbert_multiplier_closed p Q d U u hu hull hs hd t hm)
  have ho : hilbertFamilyToCompletion _ U (f - t) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
    have he : hilbertFamilyToCompletion _ U (f - t) =
        hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t :=
      (hilbertFamilyCompletionLinearMap _ U).map_sub f t
    rw [he, ht]
    exact (mixedDualHilbertSubspace p Q d U).sub_starProjection_mem_orthogonal _
  have h := mixedDualHilbert_multiplier_orthogonal p Q d U u hu hull (f - t) ho
  have he : hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu (f - t)) =
      hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu f) -
        hilbertFamilyToCompletion _ U (weightedHaarMultiplier p u hu t) :=
    ((hilbertFamilyCompletionLinearMap _ U).comp (weightedHaarMultiplier p u hu)).map_sub f t
  rwa [he] at h

end Hindman168
