import Hindman168.WeightedHaarHilbert
import Mathlib.Analysis.InnerProductSpace.Orthogonal

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)

/-- Actual Hilbert images of cellwise mixed-dual convex-hull families. -/
def mixedDualHilbertGenerators :
    Set (UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  {z | ∃ f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    (∀ w c, (fun x => f.val w (c, x)) ∈ subgroupMixedDualHull (Q w) d) ∧
    hilbertFamilyToCompletion _ U f = z}

noncomputable def mixedDualHilbertSubspace :
    Submodule ℝ (UltrafilterHilbertSpace (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  (Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).topologicalClosure

theorem mixedDualHilbert_inner_zero (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g f : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hf : ∀ w c, (fun x => f.val w (c, x)) ∈ subgroupMixedDualHull (Q w) d)
    (hg : Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    inner ℝ (hilbertFamilyToCompletion _ U g) (hilbertFamilyToCompletion _ U f) = 0 := by
  have hb := Eventually.of_forall (f := (U : Filter ℕ)) (fun w => weighted_mixedDualHull_correlation_le_gowers
    (Q w) d hd (p w) (Fact.out : ∀ c, 0 ≤ p w c) (hs w)
    (fun c x => f.val w (c, x)) (hf w) (fun c x => g.val w (c, x)))
  have ha := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hb hg
  exact tendsto_nhds_unique (weightedHaarHilbert_inner_tendsto p U g f)
    ((tendsto_zero_iff_abs_tendsto_zero _).mpr ha)

theorem mixedDualHilbert_orthogonal_of_gowers_zero
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0)) :
    hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ := by
  rw [mixedDualHilbertSubspace, Submodule.orthogonal_closure, Submodule.mem_orthogonal']
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨f, hf, rfl⟩ := hz
    exact mixedDualHilbert_inner_zero p Q d U hs hd g f hf hg
  | zero => exact inner_zero_right _
  | add x y _ _ hx hy => rw [inner_add_right, hx, hy, add_zero]
  | smul r x _ hx => rw [inner_smul_right, hx, mul_zero]

theorem mixedDualHilbert_gowers_zero_of_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1)
    (ho : hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ) :
    Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0) := by
  let f := weightedHaarBoundedFamily p hs
    (fun w c x => subgroupDualFunction (Q w) d (fun y => g.val w (c, y)) x) 1 zero_le_one
    (fun w c x => subgroupDualFunction_abs_le_one (Q w) d _ (hg w c) x)
  have hf : hilbertFamilyToCompletion _ U f ∈ mixedDualHilbertGenerators p Q d U := by
    refine ⟨f, ?_, rfl⟩
    intro w c
    exact subgroupMixedDualFunction_mem_hull (Q w) d (fun _ y => g.val w (c, y))
      (fun _ _ y => hg w c y)
  have hz := (Submodule.mem_orthogonal' _ _).mp ho _
    ((Submodule.le_topologicalClosure _) (Submodule.subset_span hf))
  have ht := weightedHaarHilbert_inner_tendsto p U g f
  rw [hz] at ht
  let t := fun w => weightedSubgroupGowersValue (Q w) (p w) d (fun c x => g.val w (c, x))
  have hpw : Tendsto (fun w => t w ^ (2 ^ d)) (U : Filter ℕ) (𝓝 0) := by
    simpa only [t, weightedSubgroupGowersValue_pow _ _ (Fact.out : ∀ c, 0 ≤ p _ c) d hd,
      subgroupGowersValue_pow _ d hd, subgroupCubeAverage_dual_correlation, f,
      weightedHaarBoundedFamily] using ht
  have hl := bounded_real_ultrafilter_tendsto U t ⟨1, zero_le_one, ?_⟩
  · have he : limUnder (U : Filter ℕ) t ^ (2 ^ d) = 0 := tendsto_nhds_unique (hl.pow _) hpw
    have he0 : limUnder (U : Filter ℕ) t = 0 := eq_zero_of_pow_eq_zero he
    simpa only [he0] using hl
  · intro w
    rw [abs_of_nonneg (weightedSubgroupGowersValue_nonneg (Q w) (p w) Fact.out d hd _)]
    exact weightedSubgroupGowersValue_le_one (Q w) (p w) Fact.out (hs w) d hd _ (hg w)

theorem mixedDualHilbert_gowers_zero_iff_orthogonal
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, |g.val w (c, x)| ≤ 1) :
    Tendsto (fun w => weightedSubgroupGowersValue (Q w) (p w) d
      (fun c x => g.val w (c, x))) (U : Filter ℕ) (𝓝 0) ↔
      hilbertFamilyToCompletion _ U g ∈ (mixedDualHilbertSubspace p Q d U)ᗮ :=
  ⟨mixedDualHilbert_orthogonal_of_gowers_zero p Q d U hs hd g,
    mixedDualHilbert_gowers_zero_of_orthogonal p Q d U hs hd g hg⟩

end Hindman168
