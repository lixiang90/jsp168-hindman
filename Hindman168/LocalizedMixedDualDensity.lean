import Hindman168.WeightedHaarAlgebraProjection
import Hindman168.LocalizedMixedDualProducts
import Hindman168.MixedDualProjectionCompatibility

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)

theorem localizedMixedDualHilbert_projection_exact_representative
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      (∀ w c x, 0 ≤ t.val w (c, x) ∧ t.val w (c, x) ≤ 1) ∧
      hilbertFamilyToCompletion _ U t = (localizedMixedDualHilbertSubspace p Q d U R e).starProjection
        (hilbertFamilyToCompletion _ U f) := by
  exact weightedHaarHilbert_algebra_projection_exact_representative p U hs
    (localizedMixedDualHilbertSubspace p Q d U R e) (localizedMixedDualHilbert_one_mem p Q d U R e hs)
    (fun u hu hum g hg => localizedMixedDualHilbert_unit_product_closed p Q d U R e hs he u hu hum g hg)
    hU (localizedMixedDualFamilies p Q d U R e)
    (fun a ha => localizedMixedDualFamily_unit p Q d U R e ha) rfl f hf

/-- Unit-interval represented members of the original factor intersection
already belong to the closed span of the genuine localized dual generators. -/
theorem localizedMixedDualHilbert_unit_interval_intersection_mem
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c x, 0 ≤ f.val w (c, x) ∧ f.val w (c, x) ≤ 1)
    (hboth : hilbertFamilyToCompletion _ U f ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U) :
    hilbertFamilyToCompletion _ U f ∈ localizedMixedDualHilbertSubspace p Q d U R e := by
  let L := localizedMixedDualHilbertSubspace p Q d U R e
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  obtain ⟨t, htunit, ht⟩ := localizedMixedDualHilbert_projection_exact_representative p Q d U R e hU hs he f hf
  change H t = L.starProjection (H f) at ht
  have htm : H t ∈ L := ht ▸ L.starProjection_apply_mem (H f)
  have htint := localizedMixedDualHilbertSubspace_le_intersection p Q d U R e hs he htm
  have hrR : H (f - t) ∈ mixedDualHilbertSubspace p R e U := by
    rw [H.map_sub]
    exact Submodule.sub_mem _ hboth.2 htint.2
  have hrQ : H (f - t) ∈ mixedDualHilbertSubspace p Q d U := by
    rw [H.map_sub]
    exact Submodule.sub_mem _ hboth.1 htint.1
  have hro : H (f - t) ∈ Lᗮ := by
    rw [H.map_sub, ht]
    exact L.sub_starProjection_mem_orthogonal _
  have hrunit : ∀ w c x, |(f - t).val w (c, x)| ≤ 1 := by
    intro w c x
    change |f.val w (c, x) - t.val w (c, x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [(hf w c x).1, (htunit w c x).2],
      by linarith [(hf w c x).2, (htunit w c x).1]⟩
  have ho := localizedMixedDualHilbert_relative_orthogonal p Q d U R e hs hd (f - t) hrunit hrR hro
  have hz : H (f - t) = 0 := inner_self_eq_zero.mp ((Submodule.mem_orthogonal' _ _).mp ho _ hrQ)
  have heq : H f = H t := sub_eq_zero.mp (by rwa [← H.map_sub])
  change H f ∈ L
  rw [heq]
  exact htm

/-- The second factor projection maps the whole first factor into the localized
dual span. Its extension from bounded generators uses projection continuity. -/
theorem localizedMixedDualHilbert_projection_mem
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ mixedDualHilbertSubspace p Q d U) :
    (mixedDualHilbertSubspace p R e U).starProjection z ∈ localizedMixedDualHilbertSubspace p Q d U R e := by
  let V := mixedDualHilbertSubspace p Q d U
  let W := mixedDualHilbertSubspace p R e U
  let L := localizedMixedDualHilbertSubspace p Q d U R e
  let H := hilbertFamilyCompletionLinearMap
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U
  let T := L.comap W.starProjection.toLinearMap
  have hT : IsClosed (T : Set (UltrafilterHilbertSpace
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U)) :=
    (Submodule.span ℝ (localizedMixedDualHilbertGenerators p Q d U R e)).isClosed_topologicalClosure.preimage
      W.starProjection.continuous
  have hspan : Submodule.span ℝ (mixedDualHilbertGenerators p Q d U) ≤ T := by
    apply Submodule.span_le.mpr
    rintro z ⟨f, hf, rfl⟩
    change W.starProjection (H f) ∈ L
    let one := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => (1 : ℝ)) 1 zero_le_one (by simp)
    have honeL : H one ∈ L := localizedMixedDualHilbert_one_mem p Q d U R e hs
    have honeV : H one ∈ V := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨one, fun w _ => subgroupMixedDualHull_one_mem (Q w) d, rfl⟩)
    have honeW : H one ∈ W := (Submodule.le_topologicalClosure _)
      (Submodule.subset_span ⟨one, fun w _ => subgroupMixedDualHull_one_mem (R w) e, rfl⟩)
    have hfm : H f ∈ V := (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨f, hf, rfl⟩)
    let plus := (1 / 2 : ℝ) • (f + one)
    have hpunit : ∀ w c x, 0 ≤ plus.val w (c, x) ∧ plus.val w (c, x) ≤ 1 := by
      intro w c x
      have hb := abs_le.mp (subgroupMixedDualHull_abs_le_one (Q w) d (hf w c) x)
      change 0 ≤ (1 / 2 : ℝ) * (f.val w (c, x) + 1) ∧
        (1 / 2 : ℝ) * (f.val w (c, x) + 1) ≤ 1
      constructor <;> linarith
    have hpm : H plus ∈ V := by
      change H ((1 / 2 : ℝ) • (f + one)) ∈ V
      rw [H.map_smul, H.map_add]
      exact V.smul_mem _ (V.add_mem hfm honeV)
    obtain ⟨t, htunit, ht⟩ := mixedDualHilbert_projection_exact_representative p R e U hU hs he plus hpunit
    change H t = W.starProjection (H plus) at ht
    have htint : H t ∈ V ⊓ W := by
      constructor
      · rw [ht]
        exact mixedDualHilbert_projection_preserves_closed_space p Q d U hU hs hd R e he hpm
      · rw [ht]
        exact W.starProjection_apply_mem _
    have hplocal : W.starProjection (H plus) ∈ L := by
      rw [← ht]
      exact localizedMixedDualHilbert_unit_interval_intersection_mem p Q d U R e hU hs hd he t htunit htint
    have heq : f = (2 : ℝ) • plus - one := by
      apply Subtype.ext
      funext w x
      change f.val w x = 2 * ((1 / 2 : ℝ) * (f.val w x + 1)) - 1
      ring
    rw [heq, H.map_sub, H.map_smul, map_sub, map_smul,
      Submodule.starProjection_eq_self_iff.mpr honeW]
    exact L.sub_mem (L.smul_mem _ hplocal) honeL
  exact (Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).topologicalClosure_minimal hspan hT hz

/-- The actual localized generator span is exactly the original factor
intersection. No localized representation is assumed in this equality. -/
theorem localizedMixedDualHilbertSubspace_eq_intersection
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e) :
    localizedMixedDualHilbertSubspace p Q d U R e =
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
  apply le_antisymm (localizedMixedDualHilbertSubspace_le_intersection p Q d U R e hs he)
  intro z hz
  have hm := localizedMixedDualHilbert_projection_mem p Q d U R e hU hs hd he hz.1
  rwa [Submodule.starProjection_eq_self_iff.mpr hz.2] at hm

theorem localizedMixedDualHilbert_intersection_approximation
    (hU : (U : Filter ℕ) ≤ atTop) (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e)
    {z : UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U}
    (hz : z ∈ mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
      t ∈ Submodule.span ℝ (localizedMixedDualFamilies p Q d U R e) ∧ ∃ B : ℝ, 0 ≤ B ∧
      (∀ w c x, |t.val w (c, x)| ≤ B) ∧
      hilbertFamilyToCompletion _ U t ∈ localizedMixedDualHilbertSubspace p Q d U R e ∧
      ‖z - hilbertFamilyToCompletion _ U t‖ < ε := by
  have hm : z ∈ localizedMixedDualHilbertSubspace p Q d U R e := by
    rw [localizedMixedDualHilbertSubspace_eq_intersection p Q d U R e hU hs hd he]
    exact hz
  exact weightedHaarHilbert_generated_closed_approximation p U
    (localizedMixedDualFamilies p Q d U R e)
    (fun a ha => localizedMixedDualFamily_unit p Q d U R e ha)
    (localizedMixedDualHilbertSubspace p Q d U R e) rfl hm hε

end Hindman168
