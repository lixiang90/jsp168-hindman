import Hindman168.WeightedHaarInternalAverage
import Hindman168.MixedDualHilbertTranslation
import Hindman168.StructuredDualMultiplication

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

theorem mixedDualHilbert_unit_finset_product {ι : Type*}
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (s : Finset ι)
    (f : ι → boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ i ∈ s, ∀ w c x, |(f i).val w (c, x)| ≤ 1)
    (hf : ∀ i ∈ s, hilbertFamilyToCompletion _ U (f i) ∈ mixedDualHilbertSubspace p Q d U)
    (t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (ht : ∀ w c x, t.val w (c, x) = ∏ i ∈ s, (f i).val w (c, x)) :
    hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U := by
  induction s using Finset.induction_on generalizing t with
  | empty =>
    apply Submodule.le_topologicalClosure _
    apply Submodule.subset_span
    refine ⟨t, ?_, rfl⟩
    intro w c
    have he : (fun x => t.val w (c, x)) = (1 : G w → ℝ) := by
      funext x
      simpa only [Finset.prod_empty, Pi.one_apply] using ht w c x
    rw [he]
    exact subgroupMixedDualHull_one_mem (Q w) d
  | @insert i s hi ih =>
    have hub : ∀ w c x, |∏ j ∈ s, (f j).val w (c, x)| ≤ 1 := by
      intro w c x
      rw [Finset.abs_prod]
      exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun j hj => hu j (Finset.mem_insert_of_mem hj) w c x)
    let v := weightedHaarBoundedFamily p hs (fun w c x => ∏ j ∈ s, (f j).val w (c, x)) 1 zero_le_one hub
    have hv : hilbertFamilyToCompletion _ U v ∈ mixedDualHilbertSubspace p Q d U :=
      ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))
        (fun j hj => hf j (Finset.mem_insert_of_mem hj)) v (fun _ _ _ => rfl)
    have he : t = weightedHaarMultiplier p (fun w c x => (f i).val w (c, x))
        (hu i (Finset.mem_insert_self _ _)) v := by
      apply Subtype.ext
      funext w z
      change t.val w z = (f i).val w z * ∏ j ∈ s, (f j).val w z
      simpa only [Finset.prod_insert hi] using ht w z.1 z.2
    rw [he]
    exact mixedDualHilbert_structured_product_closed p Q d U hs hd (f i)
      (hu i (Finset.mem_insert_self _ _)) (hf i (Finset.mem_insert_self _ _)) v hv

/-- Taking a mixed dual along any second subgroup system preserves the first
closed dual subspace when all nonroot inputs belong to it and are unit bounded. -/
theorem mixedDualHilbert_internal_dual_closed
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)
    (f : Finset (Fin e) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p Q d U)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, g.val w (c, x) = subgroupMixedDualFunction (R w) e
      (fun ω y => (f ω).val w (c, y)) x) :
    hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertSubspace p Q d U := by
  let s := (Finset.univ : Finset (Finset (Fin e))).erase ∅
  let F := fun w (a : Fin e → R w) (c : κ w) (x : G w) =>
    ∏ ω ∈ s, (f ω).val w (c, x + ∑ j ∈ ω, (a j : G w))
  have hF : ∀ w a c x, |F w a c x| ≤ 1 := by
    intro w a c x
    dsimp only [F]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _)
      (fun ω hω => hu ω (Finset.mem_erase.mp hω).1 w c _)
  apply weightedHaarHilbert_internal_average_closed p hs U (mixedDualHilbertSubspace p Q d U)
    (Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).isClosed_topologicalClosure F hF
    ?_ g hg
  intro a
  let v := fun ω => weightedHaarTranslation p (fun w _ => ∑ j ∈ ω, (a w j : G w)) (f ω)
  apply mixedDualHilbert_unit_finset_product p Q d U hs hd s v
  · intro ω hω w c x
    exact hu ω (Finset.mem_erase.mp hω).1 w c _
  · intro ω hω
    exact mixedDualHilbert_translation_closed p Q d U hs hd _ (f ω) (hf ω (Finset.mem_erase.mp hω).1)
  · intro w c x
    rfl


/-- A unit represented member of the first dual space needs to be tested only
against the intersection to detect its second-system Gowers seminorm. -/
theorem mixedDualHilbert_gowers_zero_of_intersection_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hstruct : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertSubspace p Q d U)
    (ho : hilbertFamilyToCompletion _ U g ∈
      (mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)ᗮ) :
    Tendsto (fun w => weightedSubgroupGowersValue (R w) (p w) e
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  let f := weightedHaarBoundedFamily p hs
    (fun w c x => subgroupDualFunction (R w) e (fun y => g.val w (c, y)) x) 1 zero_le_one
    (fun w c x => subgroupDualFunction_abs_le_one (R w) e _ (hg w c) x)
  have hfR : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertGenerators p R e U := by
    refine ⟨f, ?_, rfl⟩
    intro w c
    exact subgroupMixedDualFunction_mem_hull (R w) e (fun _ y => g.val w (c, y))
      (fun _ _ y => hg w c y)
  have hfQ : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertSubspace p Q d U :=
    mixedDualHilbert_internal_dual_closed p Q d U hs hd R e (fun _ => g)
      (fun _ _ => hg) (fun _ _ => hstruct) f (fun _ _ _ => rfl)
  have hboth : hilbertFamilyToCompletion _ U f ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U :=
    ⟨hfQ, (Submodule.le_topologicalClosure _) (Submodule.subset_span hfR)⟩
  have hz := (Submodule.mem_orthogonal' _ _).mp ho _ hboth
  have ht := weightedHaarHilbert_inner_tendsto p U g f
  rw [hz] at ht
  let t := fun w => weightedSubgroupGowersValue (R w) (p w) e (fun c x => g.val w (c, x))
  have hpw : Tendsto (fun w => t w ^ (2 ^ e)) (U : Filter ℕ) (𝓝 0) := by
    simpa only [t, weightedSubgroupGowersValue_pow _ _ (Fact.out : ∀ c, 0 ≤ p _ c) e he,
      subgroupGowersValue_pow _ e he, subgroupCubeAverage_dual_correlation, f,
      weightedHaarBoundedFamily] using ht
  have hl := bounded_real_ultrafilter_tendsto U t ⟨1, zero_le_one, ?_⟩
  · have hzpow : limUnder (U : Filter ℕ) t ^ (2 ^ e) = 0 := tendsto_nhds_unique (hl.pow _) hpw
    have he0 : limUnder (U : Filter ℕ) t = 0 := eq_zero_of_pow_eq_zero hzpow
    simpa only [he0] using hl
  · intro w
    rw [abs_of_nonneg (weightedSubgroupGowersValue_nonneg (R w) (p w) Fact.out e he _)]
    exact weightedSubgroupGowersValue_le_one (R w) (p w) Fact.out (hs w) e he _ (hg w)

theorem mixedDualHilbert_relative_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ) (he : 0 < e)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hstruct : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertSubspace p Q d U)
    (ho : hilbertFamilyToCompletion _ U g ∈
      (mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)ᗮ) :
    hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p R e U)ᗮ :=
  mixedDualHilbert_orthogonal_of_gowers_zero p R e U hs he g
    (mixedDualHilbert_gowers_zero_of_intersection_orthogonal p Q d U hs hd R e he g hg hstruct ho)

end Hindman168
