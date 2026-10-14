import Hindman168.WeightedHaarTranslation
import Hindman168.MixedDualExactModel

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

theorem mixedDualHilbert_translation_scaled_span
    (hs : ∀ w, ∑ c, p w c = 1) (a : ∀ w, κ w → G w)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (B : ℝ) (hf : ∀ w c, ∃ v ∈ subgroupMixedDualHull (Q w) d,
      (fun x => f.val w (c, x)) = B • v) :
    hilbertFamilyToCompletion _ U (weightedHaarTranslation p a f) ∈
      Submodule.span ℝ (mixedDualHilbertGenerators p Q d U) := by
  choose v hv he using hf
  let t := weightedHaarBoundedFamily p hs (fun w c x => v w c (x + a w c)) 1 zero_le_one
    (fun w c x => subgroupMixedDualHull_abs_le_one (Q w) d (hv w c) (x + a w c))
  have ht : hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertGenerators p Q d U :=
    ⟨t, fun w c => subgroupMixedDualHull_translate_mem (Q w) d (hv w c) (a w c), rfl⟩
  have hr : weightedHaarTranslation p a f = B • t := by
    apply Subtype.ext
    funext w z
    exact congrFun (he w z.1) (z.2 + a w z.1)
  rw [hr]
  change (hilbertFamilyCompletionLinearMap _ U) (B • t) ∈ _
  rw [map_smul]
  exact Submodule.smul_mem _ B (Submodule.subset_span ht)

theorem mixedDualHilbert_translation_closed
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (a : ∀ w, κ w → G w)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertSubspace p Q d U) :
    hilbertFamilyToCompletion _ U (weightedHaarTranslation p a f) ∈ mixedDualHilbertSubspace p Q d U := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨B, _, t, _, ht, _, he⟩ := mixedDualHilbert_closed_approximation p Q d U hd hf hε
  refine ⟨hilbertFamilyToCompletion _ U (weightedHaarTranslation p a t),
    mixedDualHilbert_translation_scaled_span p Q d U hs a t B ht, ?_⟩
  rw [dist_eq_norm, weightedHaarTranslation_hilbert_distance]
  exact he

theorem mixedDualHilbert_translation_orthogonal
    (a : ∀ w, κ w → G w)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ) :
    hilbertFamilyToCompletion _ U (weightedHaarTranslation p a g) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
  rw [mixedDualHilbertSubspace, Submodule.orthogonal_closure, Submodule.mem_orthogonal']
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    rw [weightedHaarTranslation_hilbert_inner]
    apply (Submodule.mem_orthogonal' _ _).mp hg
    apply Submodule.le_topologicalClosure _
    apply Submodule.subset_span
    exact ⟨weightedHaarTranslation p (fun w c => -a w c) f,
      fun w c => subgroupMixedDualHull_translate_mem (Q w) d (hf w c) (-a w c), rfl⟩
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]

theorem mixedDualHilbert_translation_projection
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (a : ∀ w, κ w → G w)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (ht : hilbertFamilyToCompletion _ U t =
      (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f)) :
    (mixedDualHilbertSubspace p Q d U).starProjection
        (hilbertFamilyToCompletion _ U (weightedHaarTranslation p a f)) =
      hilbertFamilyToCompletion _ U (weightedHaarTranslation p a t) := by
  have hm : hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U := by
    rw [ht]
    exact Submodule.starProjection_apply_mem _ _
  apply Submodule.eq_starProjection_of_mem_orthogonal
    (mixedDualHilbert_translation_closed p Q d U hs hd a t hm)
  have ho : hilbertFamilyToCompletion _ U (f - t) ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
    have he : hilbertFamilyToCompletion _ U (f - t) =
        hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t :=
      (hilbertFamilyCompletionLinearMap _ U).map_sub f t
    rw [he, ht]
    exact (mixedDualHilbertSubspace p Q d U).sub_starProjection_mem_orthogonal _
  have h := mixedDualHilbert_translation_orthogonal p Q d U a (f - t) ho
  have he : hilbertFamilyToCompletion _ U (weightedHaarTranslation p a (f - t)) =
      hilbertFamilyToCompletion _ U (weightedHaarTranslation p a f) -
        hilbertFamilyToCompletion _ U (weightedHaarTranslation p a t) :=
    ((hilbertFamilyCompletionLinearMap _ U).comp (weightedHaarTranslation p a)).map_sub f t
  rwa [he] at h

end Hindman168
