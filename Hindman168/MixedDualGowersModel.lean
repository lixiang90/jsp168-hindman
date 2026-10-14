import Hindman168.MixedDualHilbertClipping

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- The dyadic power of the limiting Gowers value is controlled by the norm
of the genuine projection onto the actual closed dual span. -/
theorem mixedDualHilbert_gowers_power_le_projection (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1) :
    ∃ a : ℝ, 0 ≤ a ∧ a ≤ 1 ∧
      Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
        (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 a) ∧
      a ^ (2 ^ d) ≤ ‖(mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U g)‖ := by
  let f := weightedHaarBoundedFamily p hs
    (fun w c x => subgroupDualFunction (Q w) d (fun y => g.val w (c, y)) x) 1 zero_le_one
    (fun w c x => subgroupDualFunction_abs_le_one (Q w) d _ (hg w c) x)
  have hf : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertSubspace p Q d U := by
    apply Submodule.le_topologicalClosure
    apply Submodule.subset_span
    refine ⟨f, ?_, rfl⟩
    intro w c
    exact subgroupMixedDualFunction_mem_hull (Q w) d (fun _ y => g.val w (c, y))
      (fun _ _ y => hg w c y)
  have hn : ‖hilbertFamilyToCompletion _ U f‖ ≤ 1 := by
    apply hilbertFamilyToCompletion_norm_le _ U f zero_le_one
    intro w
    exact finiteMassL2_norm_le _ (weightedHaarMass_total (p w) (hs w)) _ zero_le_one
      (fun z _ => subgroupDualFunction_abs_le_one (Q w) d _ (hg w z.1) z.2)
  let t := fun w => weightedSubgroupGowersValue (Q w) (p w) d (fun c x => g.val w (c, x))
  have hnon (w : ℕ) : 0 ≤ t w := weightedSubgroupGowersValue_nonneg (Q w) (p w) Fact.out d hd _
  have hone (w : ℕ) : t w ≤ 1 := weightedSubgroupGowersValue_le_one (Q w) (p w) Fact.out (hs w) d hd _ (hg w)
  have ht := bounded_real_ultrafilter_tendsto U t ⟨1, zero_le_one,
    fun w => by rw [abs_of_nonneg (hnon w)]; exact hone w⟩
  refine ⟨limUnder (U : Filter ℕ) t, ge_of_tendsto ht (Eventually.of_forall hnon),
    le_of_tendsto ht (Eventually.of_forall hone), ht, ?_⟩
  have hp : Tendsto (fun w => t w ^ (2 ^ d)) (U : Filter ℕ)
      (𝓝 (inner ℝ (hilbertFamilyToCompletion _ U g) (hilbertFamilyToCompletion _ U f))) := by
    simpa only [t, weightedSubgroupGowersValue_pow _ _ (Fact.out : ∀ c, 0 ≤ p _ c) d hd,
      subgroupGowersValue_pow _ d hd, subgroupCubeAverage_dual_correlation, f, weightedHaarBoundedFamily]
      using weightedHaarHilbert_inner_tendsto p U g f
  have he := tendsto_nhds_unique (ht.pow (2 ^ d)) hp
  have horth := (mixedDualHilbertSubspace p Q d U).starProjection_inner_eq_zero
    (hilbertFamilyToCompletion _ U g) (hilbertFamilyToCompletion _ U f) hf
  rw [inner_sub_left, sub_eq_zero] at horth
  rw [he, horth]
  exact (le_abs_self _).trans ((abs_real_inner_le_norm _ _).trans
    ((mul_le_mul_of_nonneg_left hn (norm_nonneg _)).trans_eq (mul_one _)))

/-- A unit-interval model in the actual dual subspace with arbitrarily small
ultrafilter limiting Gowers error; the projection error retains its dyadic budget. -/
theorem mixedDualHilbert_unit_model (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U ∧
      ‖(mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) -
        hilbertFamilyToCompletion _ U t‖ < ε ^ (2 ^ d) ∧
      ∃ a : ℝ, 0 ≤ a ∧ a < ε ∧
        Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
          (fun c x => f.val w (c, x) - t.val w (c, x))) (U : Filter ℕ) (𝓝 a) := by
  obtain ⟨t, ht, hm, he⟩ := mixedDualHilbert_projection_unit_approximation p Q d U hs hd f hf
    (pow_pos hε (2 ^ d))
  have hg : ∀ w c x, |(f - t).val w (c, x)| ≤ 1 := by
    intro w c x
    change |f.val w (c, x) - t.val w (c, x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hf w c x).1, (ht w c x).2],
      by linarith [(hf w c x).2, (ht w c x).1]⟩
  obtain ⟨a, ha, _, hlim, hpow⟩ := mixedDualHilbert_gowers_power_le_projection p Q d U hs hd (f - t) hg
  have heq : (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U (f - t)) =
      (mixedDualHilbertSubspace p Q d U).starProjection (hilbertFamilyToCompletion _ U f) -
        hilbertFamilyToCompletion _ U t := by
    change (mixedDualHilbertSubspace p Q d U).starProjection ((hilbertFamilyCompletionLinearMap _ U) (f - t)) = _
    rw [map_sub, map_sub]
    exact congrArg (fun z => (mixedDualHilbertSubspace p Q d U).starProjection
      (hilbertFamilyToCompletion _ U f) - z) (Submodule.starProjection_eq_self_iff.mpr hm)
  rw [heq] at hpow
  exact ⟨t, ht, hm, he, a, ha, lt_of_pow_lt_pow_left₀ _ hε.le (hpow.trans_lt he), hlim⟩

/-- The selected model has Gowers error below the requested tolerance on a set
belonging to the same ultrafilter, without asserting ordinary eventual convergence. -/
theorem mixedDualHilbert_unit_model_eventually (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U ∧
      ∀ᶠ w in (U : Filter ℕ), weightedSubgroupGowersValue (Q w) (p w) d
        (fun c x => f.val w (c, x) - t.val w (c, x)) < ε := by
  obtain ⟨t, ht, hm, _, a, _, ha, hlim⟩ := mixedDualHilbert_unit_model p Q d U hs hd f hf hε
  exact ⟨t, ht, hm, hlim.eventually (eventually_lt_nhds ha)⟩

end Hindman168
