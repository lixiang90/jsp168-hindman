import Hindman168.NestedMixedDualSpan

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (S : Finset (Fin d))

theorem nestedMixedDualFamily_unit
    {g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))}
    (hg : g ∈ nestedMixedDualFamilies p Q d U R e S) :
    ∀ w c x, |g.val w (c, x)| ≤ 1 :=
  jointMixedDualFamily_unit p Q d U R e
    (nestedMixedDualFamilies_subset_joint p Q d U R e S hg)

/-- Inserting actual finite second-direction dual approximants at a nonroot
input preserves approximation in L2. Hence every joint first-direction dual
belongs to the closed span of genuine nested duals. -/
theorem jointMixedDualFamily_mem_nested_closed
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (hd : 0 < d) (he : 0 < e) (hS : S ≠ ∅)
    {g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))}
    (hg : g ∈ jointMixedDualFamilies p Q d U R e) :
    hilbertFamilyToCompletion _ U g ∈ nestedMixedDualHilbertSubspace p Q d U R e S := by
  obtain ⟨f, hu, hf, hval⟩ := hg
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  let F := fun w c ω y => (f ω).val w (c, y)
  have hF : ∀ w c ω, ω ≠ ∅ → ω ≠ S → ∀ y, |F w c ω y| ≤ 1 :=
    fun w c ω _ _ y => hu ω w c y
  let L := weightedMixedDualInput p Q d S hS F hF
  let T := nestedMixedDualHilbertSubspace p Q d U R e S
  have hspan : Submodule.span ℝ (jointMixedDualFamilies p R e U Q d) ≤
      T.comap (H.comp L) := by
    apply Submodule.span_le.mpr
    intro r hr
    change H (L r) ∈ T
    exact (Submodule.le_topologicalClosure _) (Submodule.subset_span
      ⟨L r, weightedMixedDualInput_mem_nested p Q d U R e S hs hd hS f hu hf r hr, rfl⟩)
  have hLg : L (f S) = g := by
    apply Subtype.ext
    funext w z
    obtain ⟨c, x⟩ := z
    rw [weightedMixedDualInput_apply, hval]
    congr 1
    funext ω y
    by_cases hω : ω = S
    · subst ω
      simp only [F, ↓reduceIte]
    · simp only [F, if_neg hω]
  have hc := (Submodule.span ℝ (nestedMixedDualHilbertGenerators p Q d U R e S)).isClosed_topologicalClosure
  apply hc.closure_eq.subset
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  obtain ⟨t, ht, _, _, _, _, herr⟩ := jointMixedDualHilbert_intersection_approximation
    p R e U Q d hU hs he hd (show H (f S) ∈
      mixedDualHilbertSubspace p R e U ⊓ mixedDualHilbertSubspace p Q d U from
        ⟨(hf S hS).2, (hf S hS).1⟩) hε
  refine ⟨H (L t), hspan ht, ?_⟩
  rw [dist_eq_norm]
  have hb := weightedMixedDualInput_hilbert_distance_le p Q d S hS F hF U (f S) t
  rw [hLg] at hb
  exact hb.trans_lt herr

/-- Genuine nested duals, with both structures retained at every input,
generate the full original factor intersection. -/
theorem nestedMixedDualHilbertSubspace_eq_intersection
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (hd : 0 < d) (he : 0 < e) (hS : S ≠ ∅) :
    nestedMixedDualHilbertSubspace p Q d U R e S =
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
  apply le_antisymm (nestedMixedDualHilbertSubspace_le_intersection p Q d U R e S hs he)
  rw [← jointMixedDualHilbertSubspace_eq_intersection p Q d U R e hU hs hd he]
  apply (Submodule.span ℝ (jointMixedDualHilbertGenerators p Q d U R e)).topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro z ⟨g, hg, rfl⟩
    exact jointMixedDualFamily_mem_nested_closed p Q d U R e S hU hs hd he hS hg
  · exact (Submodule.span ℝ (nestedMixedDualHilbertGenerators p Q d U R e S)).isClosed_topologicalClosure

theorem nestedMixedDualHilbert_intersection_approximation
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1)
    (hd : 0 < d) (he : 0 < e) (hS : S ≠ ∅)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      t ∈ Submodule.span ℝ (nestedMixedDualFamilies p Q d U R e S) ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ w c x, |t.val w (c, x)| ≤ B) ∧
      hilbertFamilyToCompletion _ U t ∈ nestedMixedDualHilbertSubspace p Q d U R e S ∧
      ‖z - hilbertFamilyToCompletion _ U t‖ < ε := by
  have hm : z ∈ nestedMixedDualHilbertSubspace p Q d U R e S := by
    rw [nestedMixedDualHilbertSubspace_eq_intersection p Q d U R e S hU hs hd he hS]
    exact hz
  exact weightedHaarHilbert_generated_closed_approximation p U
    (nestedMixedDualFamilies p Q d U R e S)
    (fun a ha => nestedMixedDualFamily_unit p Q d U R e S ha)
    (nestedMixedDualHilbertSubspace p Q d U R e S) rfl hm hε

end Hindman168
