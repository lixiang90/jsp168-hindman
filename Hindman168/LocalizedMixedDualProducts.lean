import Hindman168.LocalizedMixedDualSpan
import Hindman168.WeightedHaarGeneratedAlgebra

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)

/-- Exact products of localized actual duals lie in their closed span.
The internal averaging parameters may vary with the finite stage. -/
theorem localizedMixedDualHilbert_finite_dual_product {ι : Type*} [Fintype ι]
    (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e)
    (f : ι → Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ i ω w c x, |(f i ω).val w (c, x)| ≤ 1)
    (hf : ∀ i ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f i ω) ∈ mixedDualHilbertSubspace p R e U)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, g.val w (c, x) =
      ∏ i, subgroupMixedDualFunction (Q w) d (fun ω y => (f i ω).val w (c, y)) x) :
    hilbertFamilyToCompletion _ U g ∈ localizedMixedDualHilbertSubspace p Q d U R e := by
  let A := fun w => ι → (Fin d → Q w)
  let input := fun w (a : A w) (ω : Finset (Fin d)) (c : κ w) (y : G w) =>
    ∏ i, (f i ω).val w (c, y + ∑ j ∈ ω, (a i j : G w))
  have hi : ∀ w a ω c y, |input w a ω c y| ≤ 1 := by
    intro w a ω c y
    dsimp only [input]
    rw [Finset.abs_prod]
    exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun i _ => hu i ω w c _)
  let F := fun w (a : A w) (c : κ w) (x : G w) =>
    subgroupMixedDualFunction (Q w) d (fun ω y => input w a ω c y) x
  have hF : ∀ w a c x, |F w a c x| ≤ 1 := by
    intro w a c x
    exact subgroupMixedDualFunction_abs_le_one (Q w) d _ (fun ω _ y => hi w a ω c y) x
  apply weightedHaarHilbert_internal_average_closed p hs U
    (localizedMixedDualHilbertSubspace p Q d U R e)
    (Submodule.span ℝ (localizedMixedDualHilbertGenerators p Q d U R e)).isClosed_topologicalClosure
    F hF ?_ g ?_
  · intro a
    let t := fun ω : Finset (Fin d) => weightedHaarBoundedFamily p hs
      (fun w c y => input w (a w) ω c y) 1 zero_le_one (fun w c y => hi w (a w) ω c y)
    have ht : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (t ω) ∈ mixedDualHilbertSubspace p R e U := by
      intro ω hω
      let v := fun i : ι => weightedHaarTranslation p
        (fun w _ => ∑ j ∈ ω, (a w i j : G w)) (f i ω)
      apply mixedDualHilbert_unit_finset_product p R e U hs he Finset.univ v
      · intro i _ w c x
        exact hu i ω w c _
      · intro i _
        exact mixedDualHilbert_translation_closed p R e U hs he _ (f i ω) (hf i ω hω)
      · intro w c x
        rfl
    let C := weightedHaarBoundedFamily p hs
      (fun w c x => F w (a w) c x) 1 zero_le_one (fun w c x => hF w (a w) c x)
    have hC : C ∈ localizedMixedDualFamilies p Q d U R e :=
      localizedMixedDualFamily_mem p Q d U R e t (fun ω _ w c x => hi w (a w) ω c x) ht C
        (fun _ _ _ => rfl)
    exact (Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨C, hC, rfl⟩)
  · intro w c x
    rw [hg]
    exact subgroupMixedDualFunction_product_average (Q w) d
      (fun i ω y => (f i ω).val w (c, y)) x

theorem localizedMixedDualHilbert_generator_product {ι : Type*} [Fintype ι]
    (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e)
    (v : ι → boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hv : ∀ i, v i ∈ localizedMixedDualFamilies p Q d U R e)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, g.val w (c, x) = ∏ i, (v i).val w (c, x)) :
    hilbertFamilyToCompletion _ U g ∈ localizedMixedDualHilbertSubspace p Q d U R e := by
  choose f hu hf hval using hv
  apply localizedMixedDualHilbert_finite_dual_product p Q d U R e hs he f hu hf g
  intro w c x
  rw [hg]
  apply Finset.prod_congr rfl
  intro i _
  exact hval i w c x

/-- Among actual unit members of the second space, orthogonality to the
localized dual span already detects the first Gowers seminorm. -/
theorem localizedMixedDualHilbert_gowers_zero_of_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hR : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertSubspace p R e U)
    (ho : hilbertFamilyToCompletion _ U g ∈ (localizedMixedDualHilbertSubspace p Q d U R e)ᗮ) :
    Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  let C := weightedHaarBoundedFamily p hs
    (fun w c x => subgroupDualFunction (Q w) d (fun y => g.val w (c, y)) x) 1 zero_le_one
    (fun w c x => subgroupDualFunction_abs_le_one (Q w) d _ (hg w c) x)
  have hC : C ∈ localizedMixedDualFamilies p Q d U R e :=
    localizedMixedDualFamily_mem p Q d U R e (fun _ => g) (fun _ _ => hg)
      (fun _ _ => hR) C (fun _ _ _ => rfl)
  have hz := (Submodule.mem_orthogonal' _ _).mp ho _
    ((Submodule.le_topologicalClosure _) (Submodule.subset_span ⟨C, hC, rfl⟩))
  have ht := weightedHaarHilbert_inner_tendsto p U g C
  rw [hz] at ht
  let t := fun w => weightedSubgroupGowersValue (Q w) (p w) d (fun c x => g.val w (c, x))
  have hpw : Tendsto (fun w => t w ^ (2 ^ d)) (U : Filter ℕ) (𝓝 0) := by
    simpa only [t, weightedSubgroupGowersValue_pow _ _ (Fact.out : ∀ c, 0 ≤ p _ c) d hd,
      subgroupGowersValue_pow _ d hd, subgroupCubeAverage_dual_correlation, C,
      weightedHaarBoundedFamily] using ht
  have hl := bounded_real_ultrafilter_tendsto U t ⟨1, zero_le_one, ?_⟩
  · have hzpow : limUnder (U : Filter ℕ) t ^ (2 ^ d) = 0 := tendsto_nhds_unique (hl.pow _) hpw
    have hz0 : limUnder (U : Filter ℕ) t = 0 := eq_zero_of_pow_eq_zero hzpow
    simpa only [hz0] using hl
  · intro w
    rw [abs_of_nonneg (weightedSubgroupGowersValue_nonneg (Q w) (p w) Fact.out d hd _)]
    exact weightedSubgroupGowersValue_le_one (Q w) (p w) Fact.out (hs w) d hd _ (hg w)

theorem localizedMixedDualHilbert_relative_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (hR : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertSubspace p R e U)
    (ho : hilbertFamilyToCompletion _ U g ∈ (localizedMixedDualHilbertSubspace p Q d U R e)ᗮ) :
    hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ :=
  mixedDualHilbert_orthogonal_of_gowers_zero p Q d U hs hd g
    (localizedMixedDualHilbert_gowers_zero_of_orthogonal p Q d U R e hs hd g hg hR ho)

theorem localizedMixedDualHilbert_unit_product_closed
    (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e)
    (u : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ w c x, |u.val w (c, x)| ≤ 1)
    (hustruct : hilbertFamilyToCompletion _ U u ∈ localizedMixedDualHilbertSubspace p Q d U R e)
    (f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : hilbertFamilyToCompletion _ U f ∈ localizedMixedDualHilbertSubspace p Q d U R e) :
    hilbertFamilyToCompletion _ U (weightedHaarMultiplier p (fun w c x => u.val w (c, x)) hu f) ∈
      localizedMixedDualHilbertSubspace p Q d U R e := by
  apply weightedHaarHilbert_generated_unit_product_closed p U
    (localizedMixedDualFamilies p Q d U R e)
    (fun a ha => localizedMixedDualFamily_unit p Q d U R e ha)
    (localizedMixedDualHilbertSubspace p Q d U R e) rfl ?_ u hu hustruct f hf
  intro a ha b hb
  let v := fun i : Fin 2 => if i = 0 then a else b
  have hv : ∀ i, v i ∈ localizedMixedDualFamilies p Q d U R e := by
    intro i
    dsimp only [v]
    split_ifs <;> assumption
  apply localizedMixedDualHilbert_generator_product p Q d U R e hs he v hv
  intro w c x
  change a.val w (c, x) * b.val w (c, x) = ∏ i : Fin 2, (v i).val w (c, x)
  simp [Fin.prod_univ_two, v]

end Hindman168
