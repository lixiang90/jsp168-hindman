import Hindman168.LocalizedMixedDualDensity

namespace Hindman168
open FiniteMass Filter
open scoped BigOperators Classical Topology

variable {G κ : ℕ → Type*} [∀ w, AddCommGroup (G w)] [∀ w, Fintype (G w)]
  [∀ w, Fintype (κ w)] (p : ∀ w, κ w → ℝ) [∀ w, Fact (∀ c, 0 ≤ p w c)]
  (Q : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (Q w)] (d : ℕ) (U : Ultrafilter ℕ)
  (R : ∀ w, AddSubgroup (G w)) [∀ w, Fintype (R w)] (e : ℕ)

/-- Actual first-direction dual families with unit nonroot inputs represented
in both original factors. The unused root is normalized to be unit bounded. -/
def jointMixedDualFamilies : Set (boundedHilbertFamilies
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))) :=
  {g | ∃ f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))),
    (∀ ω w c x, |(f ω).val w (c, x)| ≤ 1) ∧
    (∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U) ∧
    ∀ w c x, g.val w (c, x) = subgroupMixedDualFunction (Q w) d
      (fun ω y => (f ω).val w (c, y)) x}

def jointMixedDualHilbertGenerators : Set (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  hilbertFamilyToCompletion _ U '' jointMixedDualFamilies p Q d U R e

noncomputable def jointMixedDualHilbertSubspace : Submodule ℝ (UltrafilterHilbertSpace
    (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))) U) :=
  (Submodule.span ℝ (jointMixedDualHilbertGenerators p Q d U R e)).topologicalClosure

instance jointMixedDualHilbertSubspace_hasProjection :
    (jointMixedDualHilbertSubspace p Q d U R e).HasOrthogonalProjection := by
  unfold jointMixedDualHilbertSubspace
  infer_instance

theorem jointMixedDualFamily_mem
    (f : Finset (Fin d) → boundedHilbertFamilies
      (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ ω, ω ≠ ∅ → ∀ w c x, |(f ω).val w (c, x)| ≤ 1)
    (hf : ∀ ω, ω ≠ ∅ → hilbertFamilyToCompletion _ U (f ω) ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)
    (g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hg : ∀ w c x, g.val w (c, x) = subgroupMixedDualFunction (Q w) d
      (fun ω y => (f ω).val w (c, y)) x) :
    g ∈ jointMixedDualFamilies p Q d U R e := by
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

theorem jointMixedDualFamilies_subset_localized :
    jointMixedDualFamilies p Q d U R e ⊆ localizedMixedDualFamilies p Q d U R e := by
  rintro g ⟨f, hu, hf, hval⟩
  exact ⟨f, hu, fun ω hω => (hf ω hω).2, hval⟩

theorem jointMixedDualFamily_unit
    {g : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w)))}
    (hg : g ∈ jointMixedDualFamilies p Q d U R e) :
    ∀ w c x, |g.val w (c, x)| ≤ 1 :=
  localizedMixedDualFamily_unit p Q d U R e (jointMixedDualFamilies_subset_localized p Q d U R e hg)

theorem jointMixedDualHilbertSubspace_le_intersection
    (hs : ∀ w, ∑ c, p w c = 1) (he : 0 < e) :
    jointMixedDualHilbertSubspace p Q d U R e ≤
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
  have hle : jointMixedDualHilbertSubspace p Q d U R e ≤ localizedMixedDualHilbertSubspace p Q d U R e :=
    Submodule.topologicalClosure_mono (Submodule.span_mono
      (Set.image_mono (jointMixedDualFamilies_subset_localized p Q d U R e)))
  exact hle.trans (localizedMixedDualHilbertSubspace_le_intersection p Q d U R e hs he)

theorem jointMixedDualHilbert_one_mem (hs : ∀ w, ∑ c, p w c = 1) :
    hilbertFamilyToCompletion _ U (weightedHaarBoundedFamily (G := G) p hs
      (fun _ _ _ => 1) 1 zero_le_one (by simp)) ∈ jointMixedDualHilbertSubspace p Q d U R e := by
  let one := weightedHaarBoundedFamily (G := G) p hs (fun _ _ _ => 1) 1 zero_le_one (by simp)
  have hQ : hilbertFamilyToCompletion _ U one ∈ mixedDualHilbertSubspace p Q d U :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span
      ⟨one, fun w _ => subgroupMixedDualHull_one_mem (Q w) d, rfl⟩)
  have hR : hilbertFamilyToCompletion _ U one ∈ mixedDualHilbertSubspace p R e U :=
    (Submodule.le_topologicalClosure _) (Submodule.subset_span
      ⟨one, fun w _ => subgroupMixedDualHull_one_mem (R w) e, rfl⟩)
  apply Submodule.le_topologicalClosure _
  apply Submodule.subset_span
  refine ⟨one, ?_, rfl⟩
  refine ⟨fun _ => one, by simp [one, weightedHaarBoundedFamily], fun _ _ => ⟨hQ, hR⟩, ?_⟩
  intro w c x
  simp only [one, weightedHaarBoundedFamily, subgroupMixedDualFunction,
    Finset.prod_const_one, finiteHaarMean_const]

/-- A finite product of translated actual unit inputs retains both factors.
The shifts may depend on the input, stage and original cell. -/
theorem mixedDualHilbert_intersection_shifted_product {ι : Type*} [Fintype ι]
    (hs : ∀ w, ∑ c, p w c = 1) (hd : 0 < d) (he : 0 < e)
    (f : ι → boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (hu : ∀ i w c x, |(f i).val w (c, x)| ≤ 1)
    (hf : ∀ i, hilbertFamilyToCompletion _ U (f i) ∈
      mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U)
    (a : ι → ∀ w, κ w → G w)
    (t : boundedHilbertFamilies (fun w => FiniteMassL2 (weightedHaarMass (G := G w) (p w))))
    (ht : ∀ w c x, t.val w (c, x) = ∏ i, (f i).val w (c, x + a i w c)) :
    hilbertFamilyToCompletion _ U t ∈ mixedDualHilbertSubspace p Q d U ⊓ mixedDualHilbertSubspace p R e U := by
  let v := fun i => weightedHaarTranslation p (a i) (f i)
  constructor
  · apply mixedDualHilbert_unit_finset_product p Q d U hs hd Finset.univ v
    · intro i _ w c x
      exact hu i w c _
    · intro i _
      exact mixedDualHilbert_translation_closed p Q d U hs hd _ (f i) (hf i).1
    · exact ht
  · apply mixedDualHilbert_unit_finset_product p R e U hs he Finset.univ v
    · intro i _ w c x
      exact hu i w c _
    · intro i _
      exact mixedDualHilbert_translation_closed p R e U hs he _ (f i) (hf i).2
    · exact ht

end Hindman168
