import Hindman168.MixedDualFunctionalCalculus
import Hindman168.FiniteMassHilbertClipping
import Hindman168.NestedProjectionEnergy

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

noncomputable def weightedHaarClipFamily (hs : ∀ w, ∑ c, p w c = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :
    boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) :=
  weightedHaarBoundedFamily p hs (fun w c x => unitIntervalClip (f.val w (c, x))) 1 zero_le_one
    (fun w c x => by rw [abs_of_nonneg (unitIntervalClip_bounds _).1]; exact (unitIntervalClip_bounds _).2)

theorem mixedDualHilbert_clip_mem (hs : ∀ w, ∑ c, p w c = 1)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (B : ℝ) (hB : 0 ≤ B) (hf : ∀ w c, ∃ u ∈ subgroupMixedDualHull (Q w) d,
      (fun x => f.val w (c, x)) = B • u) :
    hilbertFamilyToCompletion _ U (weightedHaarClipFamily p hs f) ∈ mixedDualHilbertSubspace p Q d U :=
  mixedDualHilbert_continuous_comp_mem p Q d U hs f (weightedHaarClipFamily p hs f) B hB hf
    unitIntervalClip unitIntervalClip_lipschitz.continuous.continuousOn (fun _ _ _ => rfl)

omit Q d in
theorem weightedHaarHilbert_clip_distance_le (hs : ∀ w, ∑ c, p w c = 1)
    (f t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U (weightedHaarClipFamily p hs t)‖ ≤
      ‖hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t‖ := by
  have h := le_of_tendsto_of_tendsto
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f (weightedHaarClipFamily p hs t))
    (hilbertFamilyToCompletion_norm_sub_sq_tendsto _ U f t)
    (Eventually.of_forall (fun w => (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
      (finiteMassL2_clip_distance_le (weightedHaarMass (G := G w) (p w)) (f.val w) (t.val w)
        (fun z _ => hf w z.1 z.2))))
  nlinarith [norm_nonneg (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U t),
    norm_nonneg (hilbertFamilyToCompletion _ U f - hilbertFamilyToCompletion _ U (weightedHaarClipFamily p hs t))]

instance mixedDualHilbertSubspace_hasProjection : (mixedDualHilbertSubspace p Q d U).HasOrthogonalProjection := by
  unfold mixedDualHilbertSubspace
  infer_instance

/-- For a [0,1]-valued original family, the actual dual-subspace projection has
arbitrarily close [0,1]-valued representatives lying in the same closed subspace. -/
theorem mixedDualHilbert_projection_unit_approximation (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U ∧
      ‖(mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) -
        hilbertFamilyToCompletion _ U t‖ < ε := by
  let V := mixedDualHilbertSubspace p Q d U
  obtain ⟨B, hB, t, _, ht, hm, he⟩ := mixedDualHilbert_closed_approximation p Q d U hd
    (V.starProjection_apply_mem (hilbertFamilyToCompletion _ U f)) hε
  have hc := mixedDualHilbert_clip_mem p Q d U hs t B hB ht
  refine ⟨weightedHaarClipFamily p hs t, fun _ _ _ => unitIntervalClip_bounds _, hc, ?_⟩
  exact (projection_clipping_distance_le V (hilbertFamilyToCompletion _ U f)
    (hilbertFamilyToCompletion _ U t) (hilbertFamilyToCompletion _ U (weightedHaarClipFamily p hs t))
    (Submodule.le_topologicalClosure _ hm) hc (weightedHaarHilbert_clip_distance_le p U hs f t hf)).trans_lt he

end Hindman168
