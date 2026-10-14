import Hindman168.MixedDualRecursiveLocalization

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

theorem subgroupMixedDualFunction_congr_nonroot {G : Type*} [AddCommGroup G]
    (Q : AddSubgroup G) [Fintype Q] (d : ℕ)
    (f g : Finset (Fin d) → G → ℝ)
    (hfg : ∀ ω, ω ≠ ∅ → ∀ x, f ω x = g ω x) :
    subgroupMixedDualFunction Q d f = subgroupMixedDualFunction Q d g := by
  funext x
  unfold subgroupMixedDualFunction
  congr 1
  funext v
  apply Finset.prod_congr rfl
  intro ω hω
  exact hfg ω (Finset.mem_erase.mp hω).1 _

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)

/-- Actual mixed dual families whose unit inputs belong to the other closed
dual space. The unused root input is normalized to be unit bounded as well. -/
def localizedMixedDualFamilies : Set (boundedHilbertFamilies
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :=
  {g | ∃ f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    (∀ ω w c x, |(f ω).val w (c, x)| ≤ 1) ∧
    (∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U) ∧
    ∀ w c x, g.val w (c, x) = subgroupMixedDualFunction (Q w) d
      (fun ω y => (f ω).val w (c, y)) x}

def localizedMixedDualHilbertGenerators : Set (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  hilbertFamilyToCompletion _ U '' localizedMixedDualFamilies p Q d U R e

noncomputable def localizedMixedDualHilbertSubspace : Submodule ℝ (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  (Submodule.span ℝ (localizedMixedDualHilbertGenerators p Q d U R e)).topologicalClosure

instance localizedMixedDualHilbertSubspace_hasProjection :
    (localizedMixedDualHilbertSubspace p Q d U R e).HasOrthogonalProjection := by
  unfold localizedMixedDualHilbertSubspace
  infer_instance

theorem localizedMixedDualFamily_mem
    (f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈ mixedDualHilbertSubspace p R e U)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, g.val w (c, x) = subgroupMixedDualFunction (Q w) d
      (fun ω y => (f ω).val w (c, y)) x) :
    g ∈ localizedMixedDualFamilies p Q d U R e := by
  let t := fun ω : Finset (Fin d) => if ω = ∅ then 0 else f ω
  refine ⟨t, ?_, ?_, ?_⟩
  · intro ω w c x
    by_cases hω : ω = ∅
    · have ht : t ω = 0 := by simp only [t, if_pos hω]
      rw [ht]
      change |(0 : ℝ)| ≤ 1
      norm_num
    · simpa only [t, if_neg hω] using hu ω hω w c x
  · intro ω hω
    simpa only [t, if_neg hω] using hf ω hω
  · intro w c x
    rw [hg]
    exact congrFun (subgroupMixedDualFunction_congr_nonroot (Q w) d
      (fun ω y => (f ω).val w (c, y)) (fun ω y => (t ω).val w (c, y))
      (fun ω hω y => by simp only [t, if_neg hω])) x

theorem localizedMixedDualFamily_unit
    {g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))}
    (hg : g ∈ localizedMixedDualFamilies p Q d U R e) :
    ∀ w c x, |g.val w (c, x)| ≤ 1 := by
  obtain ⟨f, hu, _, hval⟩ := hg
  intro w c x
  rw [hval]
  exact subgroupMixedDualFunction_abs_le_one (Q w) d
    (fun ω y => (f ω).val w (c, y)) (fun ω _ y => hu ω w c y) x

theorem localizedMixedDualHilbertSubspace_le_intersection
    (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e) :
    localizedMixedDualHilbertSubspace p Q d U R e ≤
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro z ⟨g, ⟨f, hu, hf, hval⟩, rfl⟩
    have hgen : hilbertFamilyToCompletion _ U g ∈ mixedDualHilbertGenerators p Q d U := by
      refine ⟨g, ?_, rfl⟩
      intro w c
      have heq : (fun x => g.val w (c, x)) =
          subgroupMixedDualFunction (Q w) d (fun ω y => (f ω).val w (c, y)) := funext (hval w c)
      rw [heq]
      exact subgroupMixedDualFunction_mem_hull (Q w) d
        (fun ω y => (f ω).val w (c, y)) (fun ω _ y => hu ω w c y)
    exact ⟨(Submodule.le_topologicalClosure _) (Submodule.subset_span hgen),
      mixedDualHilbert_internal_dual_closed p R e U hs he Q d f
        (fun ω _ => hu ω) hf g hval⟩
  · exact ((Submodule.span ℝ (mixedDualHilbertGenerators p Q d U)).isClosed_topologicalClosure).inter
      ((Submodule.span ℝ (mixedDualHilbertGenerators p R e U)).isClosed_topologicalClosure)

theorem localizedMixedDualHilbert_one_mem (hs : ∀ w, ∑ c, p w c = 1) :
    hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily (G := G) p hs
      (fun _ _ _ => 1) 1 zero_le_one (by simp)) ∈
        localizedMixedDualHilbertSubspace p Q d U R e := by
  let one := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => 1) 1 zero_le_one (by simp)
  have hR : hilbertFamilyToCompletion _ U one ∈ mixedDualHilbertSubspace p R e U := by
    apply Submodule.le_topologicalClosure _
    apply Submodule.subset_span
    exact ⟨one, fun w c => subgroupMixedDualHull_one_mem (R w) e, rfl⟩
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  refine ⟨one, ?_, rfl⟩
  refine ⟨fun _ => one, by simp [one, weightedHaarBoundedFamily], fun _ _ => hR, ?_⟩
  intro w c x
  simp only [one, weightedHaarBoundedFamily, subgroupMixedDualFunction,
    Finset.prod_const_one, finiteHaarMean_const]

end Hindman168
