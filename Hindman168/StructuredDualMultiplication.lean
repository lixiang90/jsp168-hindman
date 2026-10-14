import Hindman168.MixedDualMultiplication

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

theorem mixedDualHilbert_structured_scaled_product
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ w c x, |u.val w (c, x)| ≤ 1)
    (hustruct : hilbertFamilyToCompletion _ U u ∈ mixedDualHilbertSubspace p Q d U)
    (t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (B : ℝ) (ht : ∀ w c, ∃ v ∈ subgroupMixedDualHull (Q w) d,
      (fun x => t.val w (c, x)) = B • v) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu t)
      ∈ mixedDualHilbertSubspace p Q d U := by
  choose v hv he using ht
  have hvb : ∀ w c x, |v w c x| ≤ 1 := fun w c x => subgroupMixedDualHull_abs_le_one (Q w) d (hv w c) x
  have hm := mixedDualHilbert_multiplier_closed p Q d U v hvb hv hs hd u hustruct
  have hrep : weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu t =
      B • weightedHaarMultiplier p v hvb u := by
    apply Subtype.ext
    funext w
    funext z
    change u.val w z * t.val w z = B * (v w z.1 z.2 * u.val w z)
    have hx : t.val w z = B * v w z.1 z.2 := congrFun (he w z.1) z.2
    rw [hx]
    ring
  rw [hrep]
  change (hilbertFamilyCompletionLinearMap _ U) (B • weightedHaarMultiplier p v hvb u) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ B hm

/-- Every represented unit-bounded member of the closed dual space is a multiplier
of that space, even when it is not itself a cellwise dual-hull member. -/
theorem mixedDualHilbert_structured_product_closed
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ w c x, |u.val w (c, x)| ≤ 1)
    (hustruct : hilbertFamilyToCompletion _ U u ∈ mixedDualHilbertSubspace p Q d U)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertSubspace p Q d U) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu f)
      ∈ mixedDualHilbertSubspace p Q d U := by
  have hc := (Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).isClosed_topologicalClosure
  apply hc.closure_eq.subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨B, _, t, _, ht, _, he⟩ := mixedDualHilbert_closed_approximation p Q d U hd hf hε
  refine ⟨hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu t),
    mixedDualHilbert_structured_scaled_product p Q d U hs hd u hu hustruct t B ht, ?_⟩
  rw [dist_eq_norm]
  exact (weightedHaarMultiplier_hilbert_distance_le p U (fun w c x => u.val w (c, x)) hu f t).trans_lt he

theorem mixedDualHilbert_structured_product_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ w c x, |u.val w (c, x)| ≤ 1)
    (hustruct : hilbertFamilyToCompletion _ U u ∈ mixedDualHilbertSubspace p Q d U)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu g)
      ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
  rw [mixedDualHilbertSubspace, Submodule.orthogonal_closure, Submodule.mem_orthogonal']
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    rw [weightedHaarMultiplier_hilbert_inner]
    exact (Submodule.mem_orthogonal' _ _).mp hg _
      (mixedDualHilbert_structured_product_closed p Q d U hs hd u hu hustruct f
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨f, hf, rfl⟩)))
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]

theorem mixedDualHilbert_structured_projection_pullout
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ w c x, |u.val w (c, x)| ≤ 1)
    (hustruct : hilbertFamilyToCompletion _ U u ∈ mixedDualHilbertSubspace p Q d U)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (ht : hilbertFamilyToCompletion _ U t =
      (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f)) :
    (mixedDualHilbertSubspace p Q d U).starProjection
        (hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu f)) =
      hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu t) := by
  have hm : hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U := by
    rw [ht]
    exact Submodule.starProjection_apply_mem _ _
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (mixedDualHilbert_structured_product_closed p Q d U hs hd u hu hustruct t hm)
  have ho : hilbertFamilyToCompletion _ U (f - t) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
    have he : hilbertFamilyToCompletion _ U (f - t) =
        hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t :=
      (hilbertFamilyCompletionLinearMap _ U).map_sub f t
    rw [he, ht]
    exact (mixedDualHilbertSubspace p Q d U).sub_starProjection_mem_orthogonal _
  have h := mixedDualHilbert_structured_product_orthogonal p Q d U hs hd u hu hustruct (f - t) ho
  have he : hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu (f - t)) =
      hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu f) -
        hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu t) :=
    ((hilbertFamilyCompletionLinearMap _ U).comp
      (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu)).map_sub f t
  rwa [he] at h

end Hindman168
